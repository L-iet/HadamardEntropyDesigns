"""Compile the research note and check its data, citations and artifacts."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
PAPER = HERE / 'paper'
BUILD = HERE / '.build'
BUILD.mkdir(exist_ok=True)
source = (PAPER / 'extensions.tex').read_text(encoding='utf-8')
labels = re.findall(r'\\label\{([^}]+)\}', source)
refs = re.findall(r'\\(?:ref|eqref)\{([^}]+)\}', source)
bibs = set(re.findall(r'\\bibitem\{([^}]+)\}', source))
cites = {key for m in re.finditer(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',source) for key in m[1].split(',')}
assert len(labels) == len(set(labels))
assert set(refs) <= set(labels)
assert cites == bibs

profiles = json.loads((HERE/'data/covering.json').read_text())
for m in range(1,8):
    entries = []
    for profile in profiles:
        row = profile['rows'][m-1]
        entries.append(str(row['firstMissing']) if row['firstMissing'] is not None else '$>'+str(profile['cutoff'])+'$')
    text = str(m) + ' & ' + ' & '.join(entries) + r'\\'
    assert text in source, f'Paper/data mismatch: {text}'

for run in range(1,4):
    if os.name == 'nt':
        directory = '/mnt/'+PAPER.drive[0].lower()+PAPER.as_posix()[2:]
        command = ['wsl','--cd',directory,'--exec','sh','-lc',
                   'pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=../.build extensions.tex']
    else:
        command = ['pdflatex','-interaction=nonstopmode','-halt-on-error','-file-line-error','-output-directory=../.build','extensions.tex']
    result = subprocess.run(command,cwd=PAPER,capture_output=True,encoding='utf-8',errors='replace')
    (BUILD/f'latex-{run}.txt').write_text(result.stdout+result.stderr,encoding='utf-8')
    if result.returncode: raise SystemExit(f'LaTeX failed; inspect .build/latex-{run}.txt')
log = (BUILD/'extensions.log').read_text(encoding='utf-8',errors='replace')
for bad in [r'Overfull \\[hv]box',r'LaTeX Warning:',r'undefined',r'Missing character:',r'^!']:
    assert not re.search(bad,log,re.M), f'Typesetting issue: {bad}'
pdf = PAPER/'extensions.pdf'
shutil.copy2(BUILD/'extensions.pdf',pdf)
text = subprocess.run(['pdftotext','-layout',str(pdf),'-'],check=True,capture_output=True,
                      encoding='utf-8',errors='replace').stdout
assert '??' not in text
(BUILD/'paper-text.txt').write_text(text,encoding='utf-8')
pages = len([p for p in text.split('\f') if p.strip()])
files = sorted(PAPER.glob('*.tex')) + [pdf] + sorted((HERE/'data').glob('*.json')) + sorted((HERE/'lean').glob('*.lean'))
record = {
    'compiledAtUTC':datetime.now(timezone.utc).isoformat(),
    'pages':pages,'latexChecksPassed':True,'dataTableMatchesComputedReport':True,
    'files':{str(p.relative_to(HERE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
    'scope':{'mainHadamardExponentGrowthImproved':False,
             'paperProofs':['quantitative flatness','quantitative conditioning correction',
                            'second-order covering entropy','maximal-determinant consequence','finite radix certificate'],
             'newLeanProofs':['quantitative flatness','finite conditioning from a gap certificate'],
             'priorityEstablished':False,'existingLeanRepositoryEdited':False}
}
(HERE/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(f'Built {pdf}: {pages} pages; references and tables checked; no typesetting warnings.')
