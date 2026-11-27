# SPDX-License-Identifier: Apache-2.0
"""Build the fifth research report and run its exact finite checks."""
from pathlib import Path
from datetime import datetime, timezone
import importlib.util
import hashlib
import json
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parent
PREFIX=r'''\documentclass[11pt]{article}
\usepackage[margin=1in]{geometry}
\usepackage[T1]{fontenc}
\usepackage{lmodern,amsmath,amssymb,amsthm,mathtools,hyperref}
\setlength{\emergencystretch}{3em}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{proposition}[theorem]{Proposition}
\newcommand{\tr}{\operatorname{tr}}
\title{Sharp collision-entropy bounds and exact rounding\\for pairwise-independent sign variables}
\author{Joshua Mark\thanks{ORCID: \href{https://orcid.org/0009-0003-5905-2382}{0009-0003-5905-2382}. AI tools assisted with derivation, independent review, computation and exposition.}}
\date{20 November 2026 --- research draft; priority not established}
\begin{document}\maketitle
\begin{abstract}
We prove a residue-sensitive collision-probability bound for unbiased
pairwise-independent sign variables, with a complete equality
classification by Hadamard completion in at most three columns.
We also derive a fixed-dimension sufficient condition for a probability
distribution on sign vectors to contain an entire Hadamard matrix.
The condition combines collision probability with an explicit error
in its first and second moments. It yields positive Shannon-entropy
windows for exact extraction, and a larger existence window using
a classical seven-row completion theorem. We give a sharp collision
benchmark at forbidden orders and explicit obstructions to diagonal
balancing, natural operator capacities, convex exchangeable averaging,
and entrywise modular lifting. These results distinguish genuine
rounding certificates from relaxations that erase the sign constraints.
No construction attaining the sufficient window in every admissible
dimension is proved; the full Hadamard conjecture remains open.
Novelty has not been established by a comprehensive prior-art review.
\end{abstract}
'''
BIB={
'GP':r'''\bibitem{GP} D. Gavinsky and P. Pudl\'ak,
On the joint entropy of $d$-wise-independent variables,
Commentationes Mathematicae Universitatis Carolinae 57 (2016), 333--343.
\url{https://users.math.cas.cz/~pudlak/pairwise.pdf}.''',
'Verheiden':r'''\bibitem{Verheiden} E. P. Verheiden,
Arithmetical Properties of Combinatorial Matrices, Ph.D. thesis,
California Institute of Technology (1978), Theorem 4.5, pp. 22--23.
\url{https://thesis.caltech.edu/2899/}.''',
'CFS':r'''\bibitem{CFS} C. M. Caves, C. A. Fuchs and R. Schack,
Unknown quantum states: the quantum de Finetti representation,
Journal of Mathematical Physics 43 (2002), 4537--4559.
\url{https://arxiv.org/abs/quant-ph/0104088}.'''}


def finish(body):
    cited={x for match in re.finditer(r'\\cite\{([^}]+)\}',body) for x in match[1].split(',')}
    return '\n\\begin{thebibliography}{9}\n'+'\n'.join(BIB[key] for key in BIB if key in cited)+'\n\\end{thebibliography}\n\\end{document}\n'


def assemble():
    residue=(ROOT/'residue.tex').read_text(encoding='utf-8')
    rounding=(ROOT/'discrete/rounding.tex').read_text(encoding='utf-8')
    entropy=(ROOT/'entropy.tex').read_text(encoding='utf-8')
    completion=(ROOT/'completion.tex').read_text(encoding='utf-8')
    body=residue+rounding+entropy+completion
    shortprefix=PREFIX.split('\\begin{abstract}',1)[0]
    shortabstract=r'''\begin{abstract}
For $d\ge2$ unbiased pairwise-independent sign bits, put
$N=4\lceil(d+1)/4\rceil$. We prove collision probability at most
$1/N$, hence collision and Shannon entropy at least $\log N$.
Equality forces a uniform law on $N$ atoms and permits explicit
completion of its augmented matrix to a Hadamard matrix in at most
three columns. Conversely an order-$N$ Hadamard matrix attains the
bounds. The proof uses second moments, parity and Bessel inequality.
This gives an entropy characterization, not a proof that the equality
law exists at every admissible order. Priority remains unestablished.
\end{abstract}
'''
    (ROOT/'collision_entropy.tex').write_text(shortprefix+shortabstract+residue+finish(residue),encoding='utf-8',newline='\n')
    (ROOT/'rounding_entropy.tex').write_text(PREFIX+body+finish(body),encoding='utf-8',newline='\n')
    invariant=(ROOT/'invariant/invariant.tex').read_text(encoding='utf-8')
    exchange=(ROOT/'exchangeability/exchangeability.tex').read_text(encoding='utf-8')
    exchange=exchange.split('\\maketitle',1)[1].split('\\begin{thebibliography}',1)[0]
    body+=invariant+exchange
    ending=r'''
\section{Which step would actually prove the conjecture?}
The sufficient rounding inequality holds in the requested dimension;
unlike tensor descent it needs no dimension reduction. The missing
step is an existence theorem for distributions meeting that inequality
for every $4\mid n$. Pairwise independence alone is easy, while
concentration near the collision limit is the unresolved constraint.
Optimal min-entropy, correct marginals, positive capacities, modular
orthogonality and one-copy mixed-state entropy each lose information
needed for that concentration or for real sign cancellation.

The completion theorem gives a precise small-defect interface, but
the eight-missing-row example rules out unconditional completion of
arbitrary partial choices beyond it. A promising next question must
therefore select better partial choices, prove a concentration theorem,
or encode additional sign-sensitive constraints in an invariant or
moment formulation. None of these existence statements is proved here.
No Lean formalization, Git commit or publication was made in this pass.
'''
    (ROOT/'research.tex').write_text(PREFIX+body+ending+finish(body+ending),encoding='utf-8',newline='\n')


def main():
    assemble()
    checkers=('discrete/check.py','check_entropy.py','check_residue.py','invariant/check.py','exchangeability/check_exact.py','exchangeability/check_residue.py')
    for checker in checkers:
        subprocess.run([sys.executable,str(ROOT/checker)],cwd=ROOT,check=True)
    spec=importlib.util.spec_from_file_location('prior_build',ROOT.parent/'round3/build.py')
    compiler=importlib.util.module_from_spec(spec);spec.loader.exec_module(compiler);compiler.ROOT=ROOT
    pages={name:compiler.compile_one(ROOT/name) for name in ('collision_entropy.tex','rounding_entropy.tex','research.tex')}
    paths=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
           and '__pycache__' not in p.parts and p.suffix not in ('.aux','.log','.out')
           and p.name!='verification.json']
    record={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
            'checkersPassed':list(checkers),'typesettingChecksPassed':True,
            'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},
            'externalTheorems':{'sevenRowCompletion':'Verheiden1978 Theorem4.5, read in original scan; classification not rerun',
                                'quantumDeFinetti':'CavesFuchsSchack2002, complex Hilbert-space formulation'},
            'scope':{'hadamardConjectureProved':False,'noveltyEstablished':False,
                     'leanFormalization':False,'gitCommits':False}}
    (ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Built fifth-pass papers:',pages)


if __name__=='__main__':main()
