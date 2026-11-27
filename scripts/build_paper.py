# SPDX-License-Identifier: Apache-2.0
"""Build the complete consolidated paper and check references/typesetting."""
from pathlib import Path
import os,re,shutil,subprocess,json,hashlib
ROOT=Path(__file__).resolve().parents[1]
def main():
    paper=ROOT/'paper';build=paper/'.build';build.mkdir(exist_ok=True)
    # TeX can read a stale auxiliary file in its working directory before
    # looking in -output-directory, preventing references from converging.
    # Preserve generated files from earlier direct builds outside that path.
    for extension in ('aux','out','toc'):
        shadow=paper/('main.'+extension)
        if shadow.is_file():
            digest=hashlib.sha256(shadow.read_bytes()).hexdigest()[:12]
            shadow.replace(build/('root-shadow-'+digest+'.'+extension))
    if shutil.which('pdflatex') and (os.name!='nt' or os.environ.get('HADAMARD_NATIVE_TEX')=='1'):
        cmd=['pdflatex','-interaction=nonstopmode','-halt-on-error',
             '-file-line-error','-output-directory='+str(build),'main.tex']
        if 'miktex' in shutil.which('pdflatex').lower():
            cmd.insert(1,'--disable-installer')
    elif os.name=='nt':
        def wsl(p):return '/mnt/'+p.drive[0].lower()+p.as_posix()[2:]
        cmd=['wsl','--cd',wsl(paper),'--exec','pdflatex','-interaction=nonstopmode',
             '-halt-on-error','-file-line-error','-output-directory='+wsl(build),'main.tex']
    else:cmd=['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+str(build),'main.tex']
    for i in range(3):
        r=subprocess.run(cmd,cwd=paper,capture_output=True,text=True,encoding='utf-8',errors='replace')
        (build/f'pass-{i+1}.txt').write_text(r.stdout+r.stderr,encoding='utf-8')
        if r.returncode:raise SystemExit('LaTeX failed: '+str(build/f'pass-{i+1}.txt'))
    log=(build/'main.log').read_text(encoding='utf-8',errors='replace')
    for pattern in (r'Overfull \\[hv]box',r'LaTeX Warning:',r'Missing character:'):
        if re.search(pattern,log):raise SystemExit('Typesetting check failed: '+pattern)
    shutil.copy2(build/'main.pdf',paper/'main.pdf')
    r=subprocess.run(['pdftotext','-layout',str(paper/'main.pdf'),'-'],capture_output=True,
                     check=True,text=True,encoding='utf-8',errors='replace')
    if '??' in r.stdout:raise SystemExit('Unresolved PDF references')
    (build/'text.txt').write_text(r.stdout,encoding='utf-8')
    pages=len([x for x in r.stdout.split('\f') if x.strip()])
    data={'pages':pages,'typesettingChecksPassed':True,'pdfSHA256':hashlib.sha256((paper/'main.pdf').read_bytes()).hexdigest(),
          'sourceHashes':{p.relative_to(paper).as_posix():hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
                          for p in paper.rglob('*.tex') if '.build' not in p.parts},
          'scope':'Informal paper; formal coverage is recorded separately in ALIGNMENT.json'}
    (ROOT/'submission/paper.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(data))
if __name__=='__main__':main()
