# SPDX-License-Identifier: Apache-2.0
"""Build and exactly validate the ninth research pass."""
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
\title{Support rigidity, optimal atom exchange,\\and modular Hadamard-extension counts}
\author{Joshua Mark\thanks{ORCID: \href{https://orcid.org/0009-0003-5905-2382}{0009-0003-5905-2382}. AI tools assisted with derivation, independent review, computation and exposition.}}
\date{20 November 2026 --- research draft; priority not established}
\begin{document}\maketitle
'''
INTRO=r'''
\begin{abstract}
We continue the search for concentrated pairwise-independent laws.
An elementary binary-rank theorem forces almost complete support
replacement for low-rank candidates, even along known Hadamard orders
where moment errors vanish and nearby feasible laws exist. We give
sharp support-dependent Boolean degree criteria, including the
punctured extraction target. In the four-bit moment polytope, an
explicit circuit jump reaches an optimum and its exact barrier is
optimal among all continuous feasible paths. A modular lifting
theorem converts residue counts into exact sign-extension counts by
a column-pair correction in a specified eight-divisible order class.
These are conditional tools, finite-model constructions and structural
bounds. They do not construct the required distribution at an unknown
Hadamard order or prove the full conjecture. Priority remains unverified.
\end{abstract}
The standing extraction target is an exactly unbiased pairwise-independent
law on $N-4$ bits with collision at least $1/N-1/(1024N^4)$, for
$N\ge8$ divisible by four. The proof is preserved in
\path{../round6/collision_stability.tex}. Its exact entropy and
minimal-support prerequisites are in
\path{../round5/collision_entropy.tex}. We do not assume these inputs
exist in every dimension.
'''


def assemble():
    rank=(ROOT/'rank_rigidity.tex').read_text(encoding='utf-8')
    nonlinear=(ROOT/'nonlinear/support.tex').read_text(encoding='utf-8')
    exchange=(ROOT/'exchanges/exchanges.tex').read_text(encoding='utf-8').split('\\maketitle',1)[1].split('\\end{document}',1)[0]
    exchange='\n\\section{An optimal atom exchange and its exact global path barrier}\n'+exchange
    exchange=re.sub(r'\\(label|ref|eqref)\{([^}]+)\}',r'\\\1{exchange:\2}',exchange)
    lattice=(ROOT/'lattice/lattice.tex').read_text(encoding='utf-8')
    ending=r'''
\section{What still needs to be constructed}
The rank example is close to an exactly feasible Walsh law, but that
nearby law has too many equal-weight atoms. It is far from every
minimal-support extremizer. The nonlinear degree criteria identify
which fixed-support representations can work, conditional on
Hadamard existence; they do not supply the required row values at
unknown orders. The exact four-bit exchange solves a calibrated
finite landscape, not a general atom-replacement problem.

The modular theorem offers a concrete extension-count test, but no
uniform positivity theorem for that count has been proved. Its current
arithmetic class is divisible by eight. A full proof still needs a
construction or positivity argument at every admissible order, with
the four-modulo-eight class included. No theorem here assumes away
that missing step. All finite checks are exact arithmetic; they are
not Lean formalization. No Git commit was made.
\end{document}
'''
    (ROOT/'research.tex').write_text(PREFIX+INTRO+rank+nonlinear+exchange+lattice+ending,encoding='utf-8',newline='\n')
    short=PREFIX.replace('Support rigidity, optimal atom exchange,\\\\and modular Hadamard-extension counts',
                         'Small moment errors can require\\\\almost complete support replacement')
    (ROOT/'rank_rounding.tex').write_text(short+rank+'\n\\end{document}\n',encoding='utf-8',newline='\n')


def main():
    assemble()
    checkers=('check_rank.py','nonlinear/check.py','exchanges/check_exact.py','lattice/check.py')
    for checker in checkers:subprocess.run([sys.executable,str(ROOT/checker)],cwd=ROOT,check=True)
    spec=importlib.util.spec_from_file_location('prior_build',ROOT.parent/'round3/build.py')
    compiler=importlib.util.module_from_spec(spec);spec.loader.exec_module(compiler);compiler.ROOT=ROOT
    pages={name:compiler.compile_one(ROOT/name) for name in ('rank_rounding.tex','research.tex')}
    paths=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
           and '__pycache__' not in p.parts and p.suffix not in ('.aux','.log','.out')
           and p.name!='verification.json']
    record={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
            'checkersPassed':list(checkers),'typesettingChecksPassed':True,
            'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},
            'scope':{'hadamardConjectureProved':False,'unknownOrderDistributionConstructed':False,
                     'noveltyEstablished':False,'leanFormalization':False,'gitCommits':False}}
    (ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Built ninth-pass papers:',pages)


if __name__=='__main__':main()
