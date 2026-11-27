"""Build the standalone tensor theorem and consolidated third research pass."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess

ROOT=Path(__file__).resolve().parent


def assemble():
    geo=(ROOT/'geometry/tensor_stability.tex').read_text(encoding='utf-8')
    prefix,body=geo.split('\\begin{document}',1)
    body,bibliography=body.split('\\begin{thebibliography}',1)
    prefix=prefix.replace('\\newcommand{\\R}', '\\newcommand{\\Z}{\\mathbb Z}\n\\newcommand{\\R}',1)
    prefix=prefix.replace('Tensor powers destabilize nonflat critical points\\\\of entrywise orthogonal $p$-energies',
                          'Tensor stability and arithmetic rigidity\\\\in Hadamard-related problems')
    intro=r'''
\section*{The third research pass}
The leading result of this pass is the uniform tensor-destabilization
theorem below. It extends the earlier examples to every nonflat
critical point and every finite real exponent $p>2$. The subsequent
sections prove sharp energy floors for the entire quadratic-character
template, arithmetic lower bounds on observation-trade volume, and
uniform persistence of an exact three-row augmentation barrier.
These results advance auxiliary problems. None proves all-order
Hadamard existence, and bibliographic novelty remains unestablished.
'''
    body=body.replace('\\end{abstract}', '\\end{abstract}\n'+intro,1)
    branches='\n'.join((ROOT/p).read_text(encoding='utf-8') for p in
                      ('arithmetic/sharp_character_span.tex','trades/rigidity.tex','exchanges/tensor_barrier.tex'))
    ending=r'''
\section{What these results change}
The tensor theorem provides an exact structural characterization:
only scaled Hadamard matrices remain local minima at every self-tensor
power. It does not establish a tensor-stable point in any given
dimension or a way to bring a lifted improvement back to that dimension.
That is the missing step in any proposed Hadamard-existence application.

The character-span theorem closes a whole tuning direction: integer
rescaling and independent shifts cannot lower its energy floor.
Additional sequence structure, rather than a different choice of the
same constants, is necessary beyond the small exceptional lengths.

The trade bounds concern reduced observation trades on complete
balanced arrays. They do not exclude global symmetry operations,
unbounded-degree moves, or bounded augmentations of incomplete arrays.
Conversely, tensor persistence of exchange cost three is an exact
infinite family, not a proof that exchange costs are unbounded.

All source and code for this pass is under
\path{research/full_conjecture/round3/}. The four branch checkers use
only Python's standard library. The mathematical proofs, rather than
finite computations, establish the uniform assertions. No Lean code,
Git commits, submissions or publications were made in this pass.
'''
    source=prefix+'\\begin{document}'+body+'\n'+branches+ending+'\\begin{thebibliography}'+bibliography
    (ROOT/'research.tex').write_text(source,encoding='utf-8',newline='\n')


def compile_one(path):
    source=path.read_text(encoding='utf-8')
    labels=re.findall(r'\\label\{([^}]+)\}',source)
    assert len(labels)==len(set(labels)),path
    assert set(re.findall(r'\\(?:ref|eqref)\{([^}]+)\}',source))<=set(labels),path
    cites={x for m in re.finditer(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',source) for x in m[1].split(',')}
    assert cites==set(re.findall(r'\\bibitem\{([^}]+)\}',source)),path
    build=ROOT/'.build'/path.stem;build.mkdir(parents=True,exist_ok=True)
    for run in range(3):
        if os.name=='nt':
            directory='/mnt/'+path.drive[0].lower()+path.parent.as_posix()[2:]
            output='/mnt/'+build.drive[0].lower()+build.as_posix()[2:]
            cmd=['wsl','--cd',directory,'--exec','sh','-lc',
                 f'pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory={output} {path.name}']
        else:cmd=['pdflatex','-interaction=nonstopmode','-halt-on-error','-file-line-error',f'-output-directory={build}',path.name]
        r=subprocess.run(cmd,cwd=path.parent,capture_output=True,encoding='utf-8',errors='replace')
        (build/f'latex-{run+1}.txt').write_text(r.stdout+r.stderr,encoding='utf-8')
        if r.returncode:raise SystemExit(f'LaTeX failed: {build}/latex-{run+1}.txt')
    log=(build/(path.stem+'.log')).read_text(encoding='utf-8',errors='replace')
    for bad in (r'Overfull \\[hv]box',r'LaTeX Warning:',r'Missing character:',r'^!'):
        assert not re.search(bad,log,re.M),(path,bad)
    pdf=path.with_suffix('.pdf');shutil.copy2(build/pdf.name,pdf)
    r=subprocess.run(['pdftotext','-layout',str(pdf),'-'],capture_output=True,
                     check=True,encoding='utf-8',errors='replace')
    assert '??' not in r.stdout
    (build/'paper-text.txt').write_text(r.stdout,encoding='utf-8')
    return len([p for p in r.stdout.split('\f') if p.strip()])


def main():
    assemble()
    checks={}
    for name in ('geometry/checks.json','arithmetic/checks.json','trades/rigidity_checks.json','exchanges/checks.json'):
        obj=json.loads((ROOT/name).read_text(encoding='utf-8'));assert obj['passed'],name
        checks[name]=True
    pages={}
    for source in (ROOT/'geometry/tensor_stability.tex',ROOT/'research.tex'):
        pages[str(source.relative_to(ROOT))]=compile_one(source)
    files=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
           and '__pycache__' not in p.parts and p!=ROOT/'verification.json']
    record={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
            'branchChecksPassed':checks,'typesettingChecksPassed':True,
            'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)},
            'scope':{'tensorDestabilization':'paper proof for every real finite p>2; exact rational checks for integer p',
                     'hadamardConjectureProved':False,'noveltyEstablished':False,'leanFormalization':False,
                     'existingLeanRepositoryEdited':False}}
    (ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Built research PDFs:',pages)


if __name__=='__main__':main()
