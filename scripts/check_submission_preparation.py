# SPDX-License-Identifier: Apache-2.0
"""Check preparation of the stated verified scope, distinct from registry acceptance."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,os,subprocess,sys
from submission_scope import validate
ROOT=Path(__file__).resolve().parents[1]
read=lambda f:json.loads(f.read_text(encoding='utf-8'))
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
canonical=lambda f:hashlib.sha256(f.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--require-sandbox',action='store_true')
    args=parser.parse_args();errors=[]
    try:scope,configurations,scopeErrors=validate(ROOT);errors.extend(scopeErrors)
    except (OSError,ValueError,KeyError,TypeError) as exc:print('Scope validation failed:',exc);return 1
    structural=subprocess.run([sys.executable,'scripts/check_submission.py'],cwd=ROOT,capture_output=True,text=True,encoding='utf-8')
    try:
        data=json.loads(structural.stdout);errors.extend(data.get('errors',[]))
        if structural.returncode and not data.get('errors'):errors.append('Structural checker failed')
    except ValueError:errors.append('Structural checker returned invalid output: '+structural.stdout[-500:])
    for script in ['audit_mathlib_licenses.py','validate_metadata.py']:
        checked=subprocess.run([sys.executable,'scripts/'+script],cwd=ROOT,capture_output=True,text=True,encoding='utf-8')
        if checked.returncode:errors.append(script+' failed: '+(checked.stdout+checked.stderr)[-600:])
    lakefiles=[ROOT/n for n in ['lakefile.toml','lakefile.lean'] if (ROOT/n).is_file()]
    if len(lakefiles)!=1:errors.append('Palomar requires exactly one Lakefile')
    if any(f.stat().st_size>1024**2 for f in lakefiles):errors.append('Lakefile exceeds Palomar limit')
    sourceBytes=0
    for directory,children,files in os.walk(ROOT):
        children[:]=[n for n in children if n not in {'.git','.lake','.proof-tools','.build','__pycache__'}]
        for name in files:
            file=Path(directory)/name
            if file.is_file() and not file.is_symlink():sourceBytes+=file.stat().st_size
    if sourceBytes>500*1024**2:errors.append('Proposed source tree exceeds Palomar500MiB limit')
    for group in configurations:
        challenge=ROOT/Path(*group['config']['challenge_module'].split('.')).with_suffix('.lean')
        raw=challenge.read_bytes()
        if len(raw)>102400 or len(raw.splitlines())>1000:errors.append('Challenge exceeds Palomar byte/line limit: '+group['id'])
    hashes=read(ROOT/'submission/proof-hashes.json')
    for name,digest in hashes.items():
        if not (ROOT/name).is_file() or canonical(ROOT/name)!=digest:errors.append('Source/config snapshot mismatch: '+name)
    expected={n for g in configurations for n in g['config']['theorem_names']+g['config'].get('definition_names',[])}
    build=read(ROOT/'submission/build.json');audit=read(ROOT/'submission/axioms.json')
    if build.get('status')!='passed' or build.get('proofHashes')!=hashes:errors.append('Missing current full build')
    if audit.get('status')!='passed' or audit.get('proofHashes')!=hashes or set(audit.get('declarations',{}))!=expected:errors.append('Missing current complete axiom audit')
    if any(set(v)-{'propext','Classical.choice','Quot.sound'} for v in audit.get('declarations',{}).values()):errors.append('Additional axioms')
    for group in configurations:
        config=group['config']
        if set(config['permitted_axioms'])-{'propext','Classical.choice','Quot.sound'}:errors.append('Nonstandard configured axioms: '+group['id'])
        if config.get('enable_nanoda') is not True:errors.append('NanoDa not enabled: '+group['id'])
        path=ROOT/group['sandboxReport' if args.require_sandbox else 'localReport']
        if not path.is_file():errors.append('Missing comparison evidence: '+group['id']);continue
        result=read(path)
        if result.get('status')!='passed' or result.get('leanKernelAccepted') is not True or result.get('nanodaAccepted') is not True:errors.append('Both kernels have not accepted: '+group['id'])
        if result.get('proofHashes')!=hashes:errors.append('Comparison source binding stale: '+group['id'])
        if result.get('theoremNames')!=config['theorem_names'] or result.get('definitionNames')!=config.get('definition_names',[]):errors.append('Comparison declaration coverage mismatch: '+group['id'])
        if args.require_sandbox and result.get('sandboxedSourceBuild') is not True:errors.append('Missing sandboxed comparison: '+group['id'])
        if not args.require_sandbox:
            for role in ['challenge','solution']:
                export=ROOT/group['exportDirectory']/(role+'.ndjson')
                if not export.is_file() or sha(export)!=result.get('exports',{}).get(role):errors.append('Fresh export binding missing: '+group['id']+'/'+role)
    paper=read(ROOT/'submission/paper.json')
    if not paper.get('typesettingChecksPassed'):errors.append('Paper typesetting not checked')
    for name,digest in paper.get('sourceHashes',{}).items():
        if not (ROOT/'paper'/name).is_file() or canonical(ROOT/'paper'/name)!=digest:errors.append('Paper source binding stale: '+name)
    pdf=ROOT/'paper/main.pdf'
    if not pdf.is_file() or sha(pdf)!=paper.get('pdfSHA256'):errors.append('Paper PDF binding stale')
    result={'status':'passed' if not errors else 'failed','checkedAtUTC':datetime.now(timezone.utc).isoformat(),
        'scope':'Configured verified declarations only; excluded paper results are expressly not submitted',
        'verifiedPrincipalClaims':len(scope['submittedPrincipalClaims']),'totalPrincipalClaims':scope['principalClaimCount'],
        'unsubmittedPrincipalClaims':[c['id'] for c in scope['unsubmittedPrincipalClaims']],
        'comparisonGroups':[g['id'] for g in configurations],'sandboxedComparisonRequired':args.require_sandbox,
        'proposedSourceTreeBytes':sourceBytes,
        'preparedForSubmission':not errors,'registryVerified':False,'registrationPerformed':False,
        'requiresPublicImmutableCommit':True,'errors':errors,'proofHashes':hashes}
    path=ROOT/'submission'/('sandboxed-preparation.json' if args.require_sandbox else 'submission-preparation.json')
    path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in result.items() if k!='proofHashes'},indent=2))
    return 1 if errors else 0
if __name__=='__main__':raise SystemExit(main())
