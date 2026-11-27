# SPDX-License-Identifier: Apache-2.0
"""Bind public source/config snapshots only after real builds and axiom audits."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,subprocess,sys
from submission_scope import groups
ROOT=Path(__file__).resolve().parents[1]
EXCLUDE={'.git','.lake','.proof-tools','artifacts','__pycache__','.build'}
def snapshot():
    previous=ROOT/'submission/proof-hashes.json'
    names=set(json.loads(previous.read_text(encoding='utf-8'))) if previous.exists() else set()
    names.update(['lean-toolchain','lake-manifest.json','formalization.yaml','paper/ALIGNMENT.json','submission/SCOPE.json'])
    names.update(g['path'] for g in groups(ROOT))
    names.add('lakefile.lean' if (ROOT/'lakefile.lean').is_file() else 'lakefile.toml')
    if (ROOT/'submission/comparison-groups.json').exists():names.add('submission/comparison-groups.json')
    for directory,children,files in os.walk(ROOT):
        children[:]=[n for n in children if n not in EXCLUDE]
        names.update((Path(directory)/n).relative_to(ROOT).as_posix() for n in files if n.endswith('.lean'))
    names.update(f.relative_to(ROOT).as_posix() for f in (ROOT/'scripts').glob('*.py'))
    if not (ROOT/'lakefile.toml').exists():names.discard('lakefile.toml')
    if (ROOT/'submission/lake-catalogue.toml').exists():names.add('submission/lake-catalogue.toml')
    return {n:hashlib.sha256((ROOT/n).read_bytes().replace(b'\r\n',b'\n')).hexdigest() for n in sorted(names)}
def write(path,data):path.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
def main():
    selected=groups(ROOT);before=snapshot()
    modules=list(dict.fromkeys(g['config'][role+'_module'] for g in selected for role in ['challenge','solution']))
    commands=[['lake','build'],['lake','build',*modules],[sys.executable,'scripts/audit_axioms.py']]
    for command in commands:subprocess.run(command,cwd=ROOT,check=True)
    after=snapshot()
    if before!=after:raise SystemExit('Source/config changed during build/audit; no snapshot recorded')
    audit=json.loads((ROOT/'submission/axioms.json').read_text(encoding='utf-8'))
    expected={n for g in selected for n in g['config']['theorem_names']+g['config'].get('definition_names',[])}
    assert audit['status']=='passed' and set(audit['declarations'])==expected
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in audit['declarations'].values())
    write(ROOT/'submission/proof-hashes.json',after)
    audit['proofHashes']=after;write(ROOT/'submission/axioms.json',audit)
    write(ROOT/'submission/build.json',{'status':'passed','checkedAtUTC':datetime.now(timezone.utc).isoformat(),
        'proofHashes':after,'commands':commands,
        'comparisonGroups':[{'id':g['id'],'config':g['path']} for g in selected],
        'scope':'Actual ordinary builds and complete configured-declaration axiom audit, with source/config unchanged before and after.'})
    print('Recorded',len(after),'verified source/config hashes and',len(expected),'axiom profiles.')
if __name__=='__main__':main()
