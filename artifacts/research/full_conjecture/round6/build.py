# SPDX-License-Identifier: Apache-2.0
"""Compile the sixth research pass; finite validation uses exact arithmetic."""
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
\title{Quantitative rounding, collision traps,\\and Hadamard repair budgets}
\author{Joshua Mark\thanks{ORCID: \href{https://orcid.org/0009-0003-5905-2382}{0009-0003-5905-2382}. AI tools assisted with derivation, independent review, computation and exposition.}}
\date{20 November 2026 --- research draft; priority not established}
\begin{document}\maketitle
'''
INTRO=r'''
\begin{abstract}
Following the residue-sensitive entropy characterization, we investigate
the missing attainment step. We prove an explicit near-equality
rounding theorem, exhibit arbitrarily poor strict local collision
maxima in dimensions with known Hadamard matrices, quantify the
entropy cost of full coordinate permutation symmetry, and give a
sharp exchange budget with constructive repairs of repeated seeds.
These results distinguish attainable extraction certificates from
optimization and symmetry strategies that cannot force them. None
establishes the needed near-extremal distributions at every admissible
order; the full Hadamard conjecture remains open. Priority is not
asserted without further review of the related literature.
\end{abstract}
The preceding research pass proves the following standing fact:
for $d\ge2$ unbiased pairwise-independent sign bits, put
$N=4\lceil(d+1)/4\rceil$. Then $C=\sum_xw_x^2\le1/N$ and
$H(w)\ge\log N$. Equality forces uniform support of size $N$
and explicit completion of the augmented sign rows to a Hadamard
matrix in at most three columns. Conversely $H(N)$ gives equality.
That proof is preserved in \path{../round5/collision_entropy.tex}.
It is an equality classification, not an attainment theorem.
'''
END=r'''
\section{What remains necessary for a full existence proof}
The rounding theorem makes an explicit small collision deficit
sufficient, but does not construct its input. The bad local maxima
show that ordinary continuous collision ascent can stop far short of
the optimum even at known orders. Full coordinate symmetrization
instead forces nearly maximal Shannon entropy. Neither operation
supplies a general attainment argument.

The repeated-seed family is a constructive example where local
augmentation and global completion cost differ. Its repair depends
on recognizable finite-array structure; no theorem identifies that
structure inside arbitrary partial Hadamard matrices. Its residual
Gram calculation also separates integral completion from sign
completion. A useful next result must prove a near-extremal
construction, a global optimization principle that bypasses the
certified traps, or a structural repair rule beyond these special
families. No such universal principle is assumed here.

The written proofs establish the uniform statements. Exact checkers
are supporting finite checks, not Lean verification or a substitute
for the proofs. No Git commit or external publication was made.
\end{document}
'''


def assemble():
    stability=(ROOT/'stability/stability.tex').read_text(encoding='utf-8').split('\\maketitle',1)[1].split('\\end{document}',1)[0]
    stability='\n\\section{An explicit stability and extraction theorem}\n'+stability
    stability=re.sub(r'\\(label|ref|eqref)\{([^}]+)\}',r'\\\1{stability:\2}',stability)
    traps=(ROOT/'attainment/traps.tex').read_text(encoding='utf-8')
    symmetry=(ROOT/'symmetry.tex').read_text(encoding='utf-8')
    completion=(ROOT/'completion/completion.tex').read_text(encoding='utf-8')
    (ROOT/'research.tex').write_text(PREFIX+INTRO+stability+traps+symmetry+completion+END,encoding='utf-8',newline='\n')
    short=PREFIX.replace('Quantitative rounding, collision traps,\\\\and Hadamard repair budgets',
                         'Explicit rounding from near-extremal\\\\collision probability')
    (ROOT/'collision_stability.tex').write_text(short+stability+'\n\\end{document}\n',encoding='utf-8',newline='\n')


def main():
    assemble()
    checkers=('stability/check_exact.py','attainment/check.py','check_symmetry.py','completion/check.py')
    for checker in checkers:subprocess.run([sys.executable,str(ROOT/checker)],cwd=ROOT,check=True)
    spec=importlib.util.spec_from_file_location('prior_build',ROOT.parent/'round3/build.py')
    compiler=importlib.util.module_from_spec(spec);spec.loader.exec_module(compiler);compiler.ROOT=ROOT
    pages={name:compiler.compile_one(ROOT/name) for name in ('collision_stability.tex','research.tex')}
    paths=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
           and '__pycache__' not in p.parts and p.suffix not in ('.aux','.log','.out')
           and p.name!='verification.json']
    record={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
            'checkersPassed':list(checkers),'typesettingChecksPassed':True,
            'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},
            'scope':{'hadamardConjectureProved':False,'universalAttainmentProved':False,
                     'noveltyEstablished':False,'leanFormalization':False,'gitCommits':False}}
    (ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Built sixth-pass papers:',pages)


if __name__=='__main__':main()
