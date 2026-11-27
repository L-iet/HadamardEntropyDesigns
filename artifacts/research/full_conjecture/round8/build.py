# SPDX-License-Identifier: Apache-2.0
"""Assemble and validate the eighth research pass, preserving earlier files."""
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
\title{Nonlinear seed encodings, adaptive weights,\\and entropy-order transitions}
\author{Joshua Mark\thanks{ORCID: \href{https://orcid.org/0009-0003-5905-2382}{0009-0003-5905-2382}. AI tools assisted with derivation, independent review, computation and exposition.}}
\date{20 November 2026 --- research draft; priority not established}
\begin{document}\maketitle
'''
INTRO=r'''
\begin{abstract}
We test nonlinear distribution constructions and adaptive moment
correction against the Hadamard extraction target. Minimal binary
encodings of the known order-twelve and order-twenty matrices need
maximum Boolean degree exactly three, and binary-rank constraints
force growing degree for large orders congruent to four modulo eight.
We give a positivity-controlled support-weight correction and show
why no reweighting can repair a failed minimal-size support.
Separately, the four-bit pairwise-independent moment polytope has an
exact R\'enyi-order transition with competing strict local optima.
A concrete partial-matrix augmentation shows why odd-kernel shortness
is not a monotone construction potential. These are benchmarks and
conditional tools; no near-extremal distribution is constructed at
an unknown Hadamard order. The full conjecture remains open, and
novelty has not been established by a comprehensive literature review.
\end{abstract}
We retain the earlier target: for $N\ge8$ divisible by four, a law on
$N-4$ unbiased pairwise-independent sign bits with collision at least
$1/N-1/(1024N^4)$ yields a Hadamard matrix. Its proof is preserved in
\path{../round6/collision_stability.tex}; the exact residue-sensitive
entropy theorem is in \path{../round5/collision_entropy.tex}.
Neither characterization assumes attainment in every dimension.
'''


def assemble():
    nonlinear=(ROOT/'nonlinear/encoding.tex').read_text(encoding='utf-8')
    weights=(ROOT/'weights/weights.tex').read_text(encoding='utf-8').split('\\maketitle',1)[1].split('\\end{document}',1)[0]
    weights='\n\\section{Adaptive support corrections and a support obstruction}\n'+weights
    phase=(ROOT/'renyi_phase.tex').read_text(encoding='utf-8')
    lattice=(ROOT/'lattice/lattice.tex').read_text(encoding='utf-8')
    ending=r'''
\section{The next existence step}
The nonlinear encodings construct exact extremal laws at classical
known orders and prove specific lower bounds on model complexity.
They do not supply an encoding whose uniform support is a Hadamard
design in an unknown order. The adaptive correction works only with
its explicit rank, range and positivity conditions; no input meeting
the extraction window at all orders has been proved.

The entropy transition and lattice repair give calibrated warnings.
Changing entropy order need not destabilize a nonglobal local
minimum, and a successful augmentation can increase odd-kernel
shortness to infinity. A global construction argument must justify
its choice of nonlinear supports, nonlocal moves, or a different
potential rather than assume those diagnostics converge.
All universal statements have written proofs; finite certificates are
checked by exact arithmetic. No Lean code or Git commit was made.
\end{document}
'''
    (ROOT/'research.tex').write_text(PREFIX+INTRO+nonlinear+weights+phase+lattice+ending,encoding='utf-8',newline='\n')
    short=PREFIX.replace('Nonlinear seed encodings, adaptive weights,\\\\and entropy-order transitions',
                         'Sharp cubic encodings of known Hadamard matrices\\\\on minimal binary seeds')
    (ROOT/'nonlinear_encodings.tex').write_text(short+nonlinear+'\n\\end{document}\n',encoding='utf-8',newline='\n')
    short=PREFIX.replace('Nonlinear seed encodings, adaptive weights,\\\\and entropy-order transitions',
                         'An exact R\\\'enyi-order transition\\\\for four pairwise-independent bits')
    (ROOT/'renyi_transition.tex').write_text(short+phase+'\n\\end{document}\n',encoding='utf-8',newline='\n')


def main():
    assemble()
    checkers=('nonlinear/check.py','weights/check_exact.py','check_renyi.py','lattice/check.py')
    for checker in checkers:subprocess.run([sys.executable,str(ROOT/checker)],cwd=ROOT,check=True)
    spec=importlib.util.spec_from_file_location('prior_build',ROOT.parent/'round3/build.py')
    compiler=importlib.util.module_from_spec(spec);spec.loader.exec_module(compiler);compiler.ROOT=ROOT
    pages={name:compiler.compile_one(ROOT/name) for name in ('nonlinear_encodings.tex','renyi_transition.tex','research.tex')}
    paths=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
           and '__pycache__' not in p.parts and p.suffix not in ('.aux','.log','.out')
           and p.name!='verification.json']
    record={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
            'checkersPassed':list(checkers),'typesettingChecksPassed':True,
            'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},
            'scope':{'hadamardConjectureProved':False,'unknownOrderDistributionConstructed':False,
                     'noveltyEstablished':False,'leanFormalization':False,'gitCommits':False}}
    (ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Built eighth-pass papers:',pages)


if __name__=='__main__':main()
