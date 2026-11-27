"""Compile the research notebook and check certificate/paper alignment."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess

ROOT=Path(__file__).resolve().parent
PAPER=ROOT/'paper'; BUILD=ROOT/'.build';BUILD.mkdir(exist_ok=True)
src=(PAPER/'research.tex').read_text(encoding='utf-8')
obj=json.loads((ROOT/'data/experiments.json').read_text(encoding='utf-8'))
cert=next(x for x in obj['partialCompletion'] if x['n']==20)['unextendibleCertificate']
table=src.split('\\begin{tabular}{l}\n')[1].split('\\end{tabular}')[0]
displayed=[line.removesuffix('\\\\') for line in table.splitlines() if line]
assert displayed==[''.join('+' if x==1 else '-' for x in row) for row in cert['rows']]
exchange=json.loads((ROOT/'data/exchange.json').read_text(encoding='utf-8'))
assert exchange['minimalDeletedRowsGlobally']==2
assert exchange['allSingleRowReplacementCounts']==[1]*12
assert ','.join(map(str,exchange['newMasks'])) in src
labels=re.findall(r'\\label\{([^}]+)\}',src)
assert len(labels)==len(set(labels))
assert set(re.findall(r'\\(?:ref|eqref)\{([^}]+)\}',src))<=set(labels)
bibs=set(re.findall(r'\\bibitem\{([^}]+)\}',src))
cites={x for m in re.finditer(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',src) for x in m[1].split(',')}
assert cites==bibs
assert json.loads((ROOT/'data/verification.json').read_text())['passed']
for i in range(3):
    if os.name=='nt':
        directory='/mnt/'+PAPER.drive[0].lower()+PAPER.as_posix()[2:]
        cmd=['wsl','--cd',directory,'--exec','sh','-lc',
             'pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=../.build research.tex']
    else:cmd=['pdflatex','-interaction=nonstopmode','-halt-on-error','-file-line-error','-output-directory=../.build','research.tex']
    r=subprocess.run(cmd,cwd=PAPER,capture_output=True,encoding='utf-8',errors='replace')
    (BUILD/f'latex-{i+1}.txt').write_text(r.stdout+r.stderr,encoding='utf-8')
    if r.returncode:raise SystemExit('LaTeX failed: inspect .build/latex-'+str(i+1)+'.txt')
log=(BUILD/'research.log').read_text(encoding='utf-8',errors='replace')
for bad in (r'Overfull \\[hv]box',r'LaTeX Warning:',r'Missing character:',r'^!'):
    assert not re.search(bad,log,re.M),bad
shutil.copy2(BUILD/'research.pdf',PAPER/'research.pdf')
r=subprocess.run(['pdftotext','-layout',str(PAPER/'research.pdf'),'-'],capture_output=True,
                 check=True,encoding='utf-8',errors='replace')
assert '??' not in r.stdout
(BUILD/'paper-text.txt').write_text(r.stdout,encoding='utf-8')
pages=len([x for x in r.stdout.split('\f') if x.strip()])
files=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
       and '__pycache__' not in p.parts and p!=ROOT/'verification.json']
record={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
        'paperMatrixMatchesCertificate':True,'latexChecksPassed':True,
        'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)},
        'scope':{'fullConjectureProved':False,'newUniversalConstruction':False,
                 'strongerNormLiftingProved':False,'priorityEstablished':False,
                 'exactFiniteCertificatesVerified':True,'leanWork':False,
                 'existingProjectEdited':False}}
(ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(f'Built {pages}-page research notebook; references, certificate alignment and typesetting checks passed.')
