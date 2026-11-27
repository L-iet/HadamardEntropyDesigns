# SPDX-License-Identifier: Apache-2.0
"""Build the seventh research pass without modifying earlier artifacts."""
from pathlib import Path
from datetime import datetime,timezone
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
\newcommand{\E}{\mathbb E}
\newcommand{\tr}{\operatorname{tr}}
\title{Constructive code escape, exact moment repair,\\and arithmetic obstructions}
\author{Joshua Mark\thanks{ORCID: \href{https://orcid.org/0009-0003-5905-2382}{0009-0003-5905-2382}. AI tools assisted with derivation, independent review, computation and exposition.}}
\date{20 November 2026 --- research draft; priority not established}
\begin{document}\maketitle
'''
INTRO=r'''
\begin{abstract}
We investigate construction of the near-extremal sign distributions
needed for Hadamard extraction. We give exact Fourier moment repair
with quantified concentration cost, and prove that even its minimal
affine buffer fails on nonisotropic uniform nearest-order candidates
at sufficiently large orders. An additive-cover theorem rules out
arbitrary reweighting of the smallest binary linear seed as a way
around its power-of-two support barrier. Conversely, explicit
character rewiring escapes all traps in a special infinite family,
with an optimal-overlap straight bridge and constructive completion.
Odd-integer lattice witnesses provide a separate repair diagnostic
whose parity and Euclidean-shortness limitations are made explicit.
No general construction of the required distribution at unknown
orders is obtained, and the full Hadamard conjecture remains open.
Novelty is not asserted pending further prior-art review.
\end{abstract}
The standing extraction target is the following. For $N\ge8$ divisible
by four, an unbiased pairwise-independent law on $N-4$ sign bits
with collision at least $1/N-1/(1024N^4)$ constructs a Hadamard
matrix of order $N$. The proof is preserved in
\path{../round6/collision_stability.tex}. This pass tests actual
construction and correction mechanisms against that target, rather
than assuming its input exists.
'''


def assemble():
    correction=(ROOT/'correction/correction.tex').read_text(encoding='utf-8').split('\\maketitle',1)[1].split('\\end{document}',1)[0]
    correction='\n\\section{Exact correction of low-order moments}\n'+correction
    correction=re.sub(r'\\(label|ref|eqref)\{([^}]+)\}',r'\\\1{correction:\2}',correction)
    buffer=(ROOT/'buffer_obstruction.tex').read_text(encoding='utf-8')
    characters=(ROOT/'character_rigidity.tex').read_text(encoding='utf-8')
    escape=(ROOT/'compression/escape.tex').read_text(encoding='utf-8')
    repair=(ROOT/'repair/repair.tex').read_text(encoding='utf-8')
    ending=r'''
\section{The remaining construction problem}
The special-family escape is a genuine construction and an optimal
straight mixture bridge, but its endpoint has power-of-two order.
Fixed linear observables in the smallest binary seed force uniformity,
and the minimal-buffer theorem prevents a uniform nonisotropic
nearest-order row candidate from reaching the extraction window by
that correction alone. The positive correction theorem instead
requires concentrated, accurately weighted inputs; their general
construction is still missing.

Arithmetic witnesses can diagnose and guide some row exchanges,
but absence of a parity obstruction need not give a sign row: a
shortest-vector issue remains in the odd kernel coset. These results
suggest testing larger or nonlinear seeds, adaptive corrections
beyond the one-buffer ansatz, and metric-aware lattice repairs.
They do not prove that any of these strategies works in every
admissible dimension. No Lean code or Git commit was made.
\end{document}
'''
    (ROOT/'research.tex').write_text(PREFIX+INTRO+correction+buffer+characters+escape+repair+ending,encoding='utf-8',newline='\n')
    short=PREFIX.replace('Constructive code escape, exact moment repair,\\\\and arithmetic obstructions',
                         'Explicit escape from character-code traps\\\\and optimal-overlap bridges')
    (ROOT/'code_escape.tex').write_text(short+escape+'\n\\end{document}\n',encoding='utf-8',newline='\n')


def main():
    assemble()
    checkers=('correction/check_exact.py','check_buffer.py','check_characters.py','compression/check.py','repair/check.py')
    for checker in checkers:subprocess.run([sys.executable,str(ROOT/checker)],cwd=ROOT,check=True)
    spec=importlib.util.spec_from_file_location('prior_build',ROOT.parent/'round3/build.py')
    compiler=importlib.util.module_from_spec(spec);spec.loader.exec_module(compiler);compiler.ROOT=ROOT
    pages={name:compiler.compile_one(ROOT/name) for name in ('code_escape.tex','research.tex')}
    paths=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
           and '__pycache__' not in p.parts and p.suffix not in ('.aux','.log','.out')
           and p.name!='verification.json']
    record={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
            'checkersPassed':list(checkers),'typesettingChecksPassed':True,
            'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},
            'scope':{'hadamardConjectureProved':False,'unknownOrderDistributionConstructed':False,
                     'noveltyEstablished':False,'leanFormalization':False,'gitCommits':False}}
    (ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Built seventh-pass papers:',pages)


if __name__=='__main__':main()
