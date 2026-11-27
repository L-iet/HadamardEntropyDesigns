"""Assemble a standalone TeX/PDF from the reviewed parallel research branches."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess

ROOT=Path(__file__).resolve().parent
PAPER=ROOT/'paper';BUILD=ROOT/'.build'/'progress';BUILD.mkdir(parents=True,exist_ok=True)


def read(path):return (ROOT/path).read_text(encoding='utf-8')


def assemble():
    ar=read('arithmetic/large_energy.tex')
    body=ar.split('\\end{abstract}',1)[1].split('\\begin{thebibliography}',1)[0]
    bib=ar.split('\\begin{thebibliography}{2}',1)[1].split('\\end{thebibliography}',1)[0]
    prefix=r'''\documentclass[11pt]{article}
\usepackage[margin=1in]{geometry}
\usepackage[T1]{fontenc}
\usepackage{lmodern,amsmath,amssymb,amsthm,mathtools,booktabs,xcolor}
\usepackage{hyperref}
\hypersetup{colorlinks=true,linkcolor=blue!45!black,citecolor=blue!45!black,urlcolor=blue!45!black,
pdfauthor={Joshua Mark},pdftitle={Parallel progress toward exact Hadamard existence}}
\setlength{\emergencystretch}{3em}
\newtheorem{proposition}{Proposition}[section]
\newtheorem{theorem}[proposition]{Theorem}
\newtheorem{corollary}[proposition]{Corollary}
\newcommand{\Z}{\mathbb Z}
\newcommand{\R}{\mathbb R}
\newcommand{\one}{\mathbf 1}
\title{Parallel progress toward exact Hadamard existence}
\author{Joshua Mark\thanks{ORCID: \href{https://orcid.org/0009-0003-5905-2382}{0009-0003-5905-2382}. AI tools assisted with parallel mathematical research, exposition and exact computation.}}
\date{20 November 2026 --- research progress note}
\begin{document}
\maketitle
\begin{abstract}
We make progress on four independent routes to the Hadamard conjecture.
A classical three-square theorem solves a uniform high-energy region of
the cyclic Hermitian norm problem, with a smaller sufficient threshold
at skew-character lengths. Integer moment analysis shows that coordinate
cube moves cannot leave any saturated Hadamard array; richer trades are
necessary. An exact order-twenty-four certificate disproves universal
two-row augmentation. A tensor construction supplies non-Hadamard strict
local minima of the quartic flattening objective at infinitely many
admissible orders. The all-order Hadamard conjecture remains unproved.
These deductions and finite certificates carry no claim of bibliographic
novelty, and none is presented as a Lean formalization.
\end{abstract}

\section{What is established and what is still missing}
The preceding research notebook posed a broader arithmetic question:
for odd $m,t$, can four coefficientwise odd elements of
$\Z[z]/(z^m-1)$ have Hermitian norm sum $4t$? Necessarily $t\ge m$.
At $t=m$, energy forces every coefficient to be a sign, and the
Goethals--Seidel transfer gives order $4m$; doubling then covers all
multiples of four if that boundary can be reached for every odd $m$.
We do not reach that boundary uniformly here.

The main positive results are the uniform sufficient thresholds
\[
 t\ge\frac{m^2+3}{4},\qquad
 t\ge\frac{m^2+6m+21}{16}
 \quad\text{when an appropriate skew character exists}.
\]
The second threshold applies to primes $m\equiv3\pmod4$. Both remain
quadratic rather than linear. They are sharp within the displayed
construction families, not asserted to be optimal for the unrestricted
norm problem. The moment branch also proves an explicit cofinite
run-count bound in each fixed coordinate dimension.

The arithmetic objects also have a direct lattice interpretation.
The same Goethals--Seidel block identity works for integral circulants:
a norm solution gives an odd integral matrix $K$ of order $4m$ with
$KK^{\mathsf T}=4tI$. Each row has $4m$ odd entries, so its squared
length is at least $4m$. Equality is exactly the sign-matrix case.
Thus the new construction gives integral scaled isometries above their
minimum possible energy; it does not attain that minimum uniformly.

The negative results identify concrete missing ingredients. Ordinary
cube-kernel generators are not a positive-conversion mechanism at the
target; two-row exchanges do not always augment a partial matrix; and
even a smooth quartic objective has strict nonglobal minima. These are
obstructions to specific methods, not to the Hadamard conjecture.
All new work remains separate from the existing Lean repository and
the earlier asymptotic manuscript.

\section{Arithmetic: a proved high-energy norm theorem}
'''
    suffix=r'''
\section{Consequences for the next research step}
The arithmetic result replaces an unrestricted search over odd
coefficients by explicit uniform constructions in a large region.
Its remaining task is to lower the threshold to the minimum energy,
not to multiply known solutions by larger odd scalars. In the
skew-character construction one channel still has a large row sum;
the all-four aligned-character shortcut is ruled out by a parity
obstruction. A successful extension must change that structure.

The moment results require trades beyond coordinate subcubes and a
positivity argument adapted to sparse saturated fibers. Their
fixed-dimension conductor bound does not control the growing diagonal
$N=d+1$. The exchange certificate raises the necessary universal
deletion allowance to three but establishes no universal upper bound.
The quartic result means that a proposed optimization proof needs a
global argument or a way to escape genuine strict local minima.

No claimed result here proves new universal Hadamard existence. The
general proof remains open in this project. The deductions have been
reviewed for their stated domains, and exact computations are reproduced
from standard-library Python scripts. The scripts are checks of finite
certificates; the infinite assertions rest on the proofs in this note.

\section{Files and verification}
Branch sources are under \path{arithmetic/}, \path{moments/},
\path{exchanges/}, and \path{geometry/}, relative to
\path{research/full_conjecture/}. Run
\path{arithmetic/verify_large_energy.py}, \path{moments/check.py},
\path{exchanges/test_cube.py}, \path{exchanges/verify.py}, and
\path{geometry/verify.py}. The full-cube exchange verifier checks all
$2^{23}$ normalized sign vectors independently of the rational
nullspace search. The geometry proof uses an analytic Hessian lower
bound, not floating-point eigenvalue tests. No external research
proof code is imported, and no Lean work or Git commits were made.

\begin{thebibliography}{9}
\small\raggedright
'''
    extra=r'''
\bibitem{ArbitraryP} T. Banica and I. Nechita,
\emph{Almost Hadamard matrices: the case of arbitrary exponents},
Discrete Appl. Math. 161 (2013), 2367--2379.
\url{https://arxiv.org/abs/1211.2669}.
\end{thebibliography}
\end{document}
'''
    content=prefix+body+read('moments/progress.tex')+read('exchanges/results.tex')+read('geometry/quartic_traps.tex')+suffix+bib+extra
    (PAPER/'parallel_progress.tex').write_text(content,encoding='utf-8',newline='\n')
    return content


def main():
    source=assemble()
    labels=re.findall(r'\\label\{([^}]+)\}',source)
    assert len(labels)==len(set(labels))
    assert set(re.findall(r'\\(?:ref|eqref)\{([^}]+)\}',source))<=set(labels)
    cites={x for m in re.finditer(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',source) for x in m[1].split(',')}
    assert cites==set(re.findall(r'\\bibitem\{([^}]+)\}',source))
    checks={}
    for path in ('arithmetic/checks.json','moments/certificates.json','exchanges/verification.json','geometry/checks.json'):
        check=json.loads(read(path));assert check['passed'];checks[path]=True
    for i in range(3):
        if os.name=='nt':
            directory='/mnt/'+PAPER.drive[0].lower()+PAPER.as_posix()[2:]
            cmd=['wsl','--cd',directory,'--exec','sh','-lc',
                 'pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=../.build/progress parallel_progress.tex']
        else:cmd=['pdflatex','-interaction=nonstopmode','-halt-on-error','-file-line-error','-output-directory=../.build/progress','parallel_progress.tex']
        r=subprocess.run(cmd,cwd=PAPER,capture_output=True,encoding='utf-8',errors='replace')
        (BUILD/f'latex-{i+1}.txt').write_text(r.stdout+r.stderr,encoding='utf-8')
        if r.returncode:raise SystemExit('LaTeX failed: inspect .build/progress/latex-'+str(i+1)+'.txt')
    log=(BUILD/'parallel_progress.log').read_text(encoding='utf-8',errors='replace')
    for bad in (r'Overfull \\[hv]box',r'LaTeX Warning:',r'Missing character:',r'^!'):
        assert not re.search(bad,log,re.M),bad
    shutil.copy2(BUILD/'parallel_progress.pdf',PAPER/'parallel_progress.pdf')
    r=subprocess.run(['pdftotext','-layout',str(PAPER/'parallel_progress.pdf'),'-'],capture_output=True,
                     check=True,encoding='utf-8',errors='replace')
    assert '??' not in r.stdout
    (BUILD/'paper-text.txt').write_text(r.stdout,encoding='utf-8')
    pages=len([x for x in r.stdout.split('\f') if x.strip()])
    files=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
           and '__pycache__' not in p.parts and p.name not in ('verification.json','progress-verification.json')]
    report={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
            'branchChecksPassed':checks,'typesettingPassed':True,
            'source':str((PAPER/'parallel_progress.tex').relative_to(ROOT)),
            'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)},
            'scope':{'fullConjectureProved':False,'minimumEnergyUniformlyReached':False,
                     'newAllOrderHadamardConstruction':False,'leanFormalization':False,
                     'noveltyEstablished':False}}
    (ROOT/'progress-verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(f'Built {pages}-page parallel progress note; all branch checks and typesetting checks passed.')


if __name__=='__main__':main()
