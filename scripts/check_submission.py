# SPDX-License-Identifier: Apache-2.0
"""Check structure; --ready additionally requires complete principal proof coverage."""
from pathlib import Path
from comparison_groups import load_groups,declaration_names
import argparse,hashlib,json,os,re,sys
from check_baseline_provenance import check_baseline_provenance
ROOT=Path(__file__).resolve().parents[1]
EXCLUDE={'.lake','.git','.proof-tools','__pycache__','.build'}

def code_only(text):
    out=list(text);i=0;depth=0;string=False
    while i<len(text):
        pair=text[i:i+2];width=1
        if depth:
            if pair=='/-':depth+=1;width=2
            elif pair=='-/':depth-=1;width=2
        elif string:
            if text[i]=='\\':width=min(2,len(text)-i)
            elif text[i]=='"':string=False
        elif pair=='/-':depth=1;width=2
        elif pair=='--':
            end=text.find('\n',i);width=(len(text) if end<0 else end)-i
        elif text[i]=='"':string=True
        else:i+=1;continue
        for j in range(i,i+width):
            if out[j] not in '\r\n':out[j]=' '
        i+=width
    if depth or string:raise ValueError('unterminated Lean comment or string')
    return ''.join(out)

def claims(record):
    for key in ('principalClaims','principal_claims','claims'):
        if key in record:return record[key]
    raise ValueError('alignment has no principal claim list')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ready',action='store_true')
    args=parser.parse_args();errors=check_baseline_provenance();pending=[];holes=0
    try:groups=load_groups(ROOT)
    except (OSError,ValueError,KeyError,TypeError) as exc:
        print(json.dumps({'leanFiles':0,'errors':['Invalid comparison groups: '+str(exc)],
            'pendingPrincipalClaims':[],'ready':False},indent=2))
        return 1
    challenge_modules={group['config']['challenge_module'] for group in groups}
    challenge_sources={module.replace('.','/')+'.lean' for module in challenge_modules}

    required=['lean-toolchain','lakefile.toml','lake-manifest.json','formalization.yaml',
              'comparator.json','LICENSE','Challenge.lean','Solution.lean','paper/main.tex','paper/ALIGNMENT.json']
    for group in groups:
        required.append(group['path'])
        required.extend(group['config'][role+'_module'].replace('.','/')+'.lean'
                        for role in ('challenge','solution'))

    for name in required:
        if not (ROOT/name).is_file():errors.append('Missing '+name)
    sources=[]
    forbidden={'.olean','.ilean','.a','.bc','.dll','.dylib','.o','.obj','.so','.trace'}
    for directory,children,files in os.walk(ROOT):
        children[:]=[x for x in children if x not in EXCLUDE]
        sources.extend(Path(directory)/x for x in files if x.endswith('.lean'))
        for name in files:
            p=Path(directory)/name
            if p.suffix in forbidden:errors.append('Compiled artifact outside .lake: '+str(p.relative_to(ROOT)))
            if p.is_file() and not p.is_symlink():
                with p.open('rb') as stream:head=stream.read(128)
                if head.startswith(b'version https://git-lfs.github.com/spec/v1'):
                    errors.append('Git LFS pointer: '+str(p.relative_to(ROOT)))
    for p in sources:
        rel=p.relative_to(ROOT).as_posix()
        if p.is_symlink():errors.append('Source symlink: '+rel);continue
        raw=p.read_text(encoding='utf-8');code=code_only(raw)
        if len(raw.splitlines())>10000:errors.append('Oversized Lean source: '+rel)
        if not code.lstrip().startswith('module'):errors.append('Missing module header: '+rel)
        if rel in challenge_sources:
            holes+=len(re.findall(r'\bsorry\b',code))
            if len(raw.splitlines())>1000 or len(raw.encode())>102400:errors.append('Oversized independent Challenge: '+rel)
        else:
            if re.search(r'\b(sorry|admit|axiom|native_decide)\b|Lean\.ofReduceBool',code):
                errors.append('Forbidden proof hole/axiom/reduction escape: '+rel)
            for imported in re.findall(r'\bimport\s+([A-Za-z0-9_.]+)',code):
                if any(imported==module or imported.startswith(module+'.') for module in challenge_modules):
                    errors.append('Proof imports independent Challenge: '+rel)

    targets=list(dict.fromkeys(name for group in groups for name in group['config'].get('theorem_names',[])))
    for group in groups:
        config=group['config']
        source=ROOT/(config['challenge_module'].replace('.','/')+'.lean')
        if source.exists():
            challenge=code_only(source.read_text(encoding='utf-8'))
            for imported in re.findall(r'\bimport\s+([A-Za-z0-9_.]+)',challenge):
                if imported.split('.')[0] not in {'Mathlib','Lean','Init','Std'}:
                    errors.append('Noncanonical independent Challenge import in '+group['id']+': '+imported)
        if not config.get('theorem_names'):errors.append('No theorem targets in group '+group['id'])
        if set(config.get('permitted_axioms',[]))-{'propext','Classical.choice','Quot.sound'}:
            errors.append('Nonstandard permitted axioms in group '+group['id'])
    meta=json.loads((ROOT/'formalization.yaml').read_text())
    for key in ('name','description','authors','responsible_maintainers','license'):
        if not meta.get('project',{}).get(key):errors.append('Missing metadata project.'+key)
    if meta.get('project',{}).get('license')!='Apache-2.0':errors.append('License metadata mismatch')
    for dep in json.loads((ROOT/'lake-manifest.json').read_text())['packages']:
        if dep.get('type')!='git' or not re.fullmatch('[0-9a-f]{40}',dep.get('rev','')):
            errors.append('Unpinned dependency '+dep.get('name','?'))
        if not dep.get('url','').startswith('https://github.com/'):errors.append('Noncanonical dependency URL')
    record=json.loads((ROOT/'paper/ALIGNMENT.json').read_text())
    for claim in claims(record):
        status=claim.get('leanStatus',claim.get('lean_status',claim.get('status','pending')))
        declarations=claim.get('leanDeclarations',claim.get('lean_declarations',[]))
        if not declarations:
            name=claim.get('declaration',claim.get('lean_declaration'))
            declarations=[name] if name else []
        if status not in ('formalized','proved','verified') or not declarations:
            pending.append(claim.get('id',claim.get('title','unnamed')))
        elif any(x not in targets for x in declarations):
            pending.append(claim.get('id','unnamed')+': missing comparison target')
    hashes_path=ROOT/'submission/proof-hashes.json'
    if hashes_path.exists():
        recorded=json.loads(hashes_path.read_text())
        current_sources={p.relative_to(ROOT).as_posix() for p in sources
                         if 'artifacts' not in p.relative_to(ROOT).parts}
        recorded_sources={rel for rel in recorded if rel.endswith('.lean')}
        if current_sources!=recorded_sources:
            errors.append('Verified source inventory changed: '+', '.join(sorted(current_sources^recorded_sources)))
        for rel,digest in recorded.items():
            if not (ROOT/rel).is_file():
                errors.append('Verified proof source missing: '+rel);continue
            if hashlib.sha256((ROOT/rel).read_bytes().replace(b'\r\n',b'\n')).hexdigest()!=digest:
                errors.append('Verified proof source changed: '+rel)
    if args.ready:
        for name in ['paper/main.pdf','submission/axioms.json','submission/build.json']+[group['sandboxReport'] for group in groups]:
            if not (ROOT/name).exists():errors.append('Missing verification artifact '+name)
        if pending:errors.append('Principal paper claims remain unformalized')
        paper_record=ROOT/'submission/paper.json'
        if not paper_record.exists():errors.append('No verified paper snapshot')
        else:
            saved=json.loads(paper_record.read_text())
            for rel,digest in saved.get('sourceHashes',{}).items():
                if hashlib.sha256((ROOT/'paper'/rel).read_bytes().replace(b'\r\n',b'\n')).hexdigest()!=digest:
                    errors.append('Paper source changed after PDF build: '+rel)
            if (ROOT/'paper/main.pdf').is_file() and hashlib.sha256((ROOT/'paper/main.pdf').read_bytes()).hexdigest()!=saved.get('pdfSHA256'):
                errors.append('Paper PDF differs from verified snapshot')
        expected=json.loads(hashes_path.read_text()) if hashes_path.exists() else None
        for group in groups:
            result=ROOT/group['sandboxReport']
            if result.exists():
                proof=json.loads(result.read_text())
                config=group['config']
                if proof.get('status')!='passed' or proof.get('leanKernelAccepted') is not True or proof.get('nanodaAccepted') is not True:
                    errors.append('Both Comparator kernels have not passed group '+group['id'])
                if proof.get('sandboxedSourceBuild') is not True:
                    errors.append('Missing sandboxed source-build evidence for group '+group['id'])
                if proof.get('proofHashes')!=expected:
                    errors.append('Comparator proof snapshot is stale for group '+group['id'])
                if (proof.get('configPath')!=group['path'] or proof.get('comparisonGroup')!=group['id'] or
                    proof.get('theoremNames')!=config['theorem_names'] or
                    proof.get('definitionNames')!=config.get('definition_names',[])):
                    errors.append('Comparator target coverage mismatch for group '+group['id'])
        axiom_path=ROOT/'submission/axioms.json'
        if axiom_path.exists():
            audit=json.loads(axiom_path.read_text())
            if audit.get('status')!='passed' or set(audit.get('declarations',{}))!=set(declaration_names(groups)):
                errors.append('Axiom audit does not cover every comparison group')
            if audit.get('proofHashes')!=expected:
                errors.append('Axiom audit source snapshot is stale')
        build_path=ROOT/'submission/build.json'
        if build_path.exists():
            build=json.loads(build_path.read_text())
            if build.get('status')!='passed' or build.get('proofHashes')!=expected:
                errors.append('Build source snapshot is stale')

    report={'leanFiles':len(sources),'intentionalChallengePlaceholders':holes,'errors':errors,
            'pendingPrincipalClaims':pending,'ready':args.ready and not errors and not pending,
            'comparisonGroups':[{'id':group['id'],'config':group['path']} for group in groups]}
    print(json.dumps(report,indent=2))
    return 1 if errors else 0

if __name__=='__main__':raise SystemExit(main())
