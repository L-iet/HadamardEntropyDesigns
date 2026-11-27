# SPDX-License-Identifier: Apache-2.0
"""Assemble and compile the fourth research pass without editing prior passes."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
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
\title{Tensor-stable extrema and quantitative flatness\\over the real and complex fields}
\author{Joshua Mark\thanks{ORCID: \href{https://orcid.org/0009-0003-5905-2382}{0009-0003-5905-2382}. AI tools assisted with derivation, independent review, computation and exposition.}}
\date{20 November 2026 --- research draft; priority not established}
\begin{document}
'''
BIB=r'''
\begin{thebibliography}{9}
\bibitem{BN} T. Banica and I. Nechita, Almost Hadamard matrices:
the case of arbitrary exponents, Discrete Applied Mathematics 161
(2013), 2367--2379. \url{https://arxiv.org/abs/1211.2669}.
\bibitem{BNZ} T. Banica, I. Nechita and K. \.{Z}yczkowski,
Almost Hadamard matrices: general theory and examples,
Open Systems and Information Dynamics 19 (2012).
\url{https://arxiv.org/abs/1202.2025}.
\bibitem{Complex} T. Banica and I. Nechita,
Almost Hadamard matrices with complex entries (2017).
\url{https://arxiv.org/abs/1702.02220}.
\end{thebibliography}
\end{document}
'''


def assemble():
    core=(ROOT/'trace_body.tex').read_text(encoding='utf-8')
    quant=(ROOT/'quantitative.tex').read_text(encoding='utf-8')
    (ROOT/'tensor_trace.tex').write_text(PREFIX+core+quant+BIB,encoding='utf-8',newline='\n')
    activation=(ROOT/'sharpen/activation.tex').read_text(encoding='utf-8').split('\\maketitle',1)[1].split('\\end{document}',1)[0]
    activation=re.sub(r'\\(label|ref|eqref)\{([^}]+)\}',r'\\\1{activation:\2}',activation)
    activation='\n\\section{Exact activation thresholds and delayed instability}\n'+activation
    setup=r'''
\section{Factored directions for comparison}
For the following refinement, let $U\in O(n)$ be critical, put
$W=|U|^{p-2}\circ U$ and $M=U^TW=M^T$, and define
\[
 T(V)=\sum_{ij}|u_{ij}|^{p-2}(UV)_{ij}^2,
 \qquad S(V)=\tr(MV^TV).
\]
The second variation in a skew generator is $p((p-1)T-S)$.
The symmetric and skew orthonormal basis trace sums are respectively
$((r+q)/2,(n+1)q/2)$ and $((r-q)/2,(n-1)q/2)$ for $(T,S)$.
Since $r<nq$, the ratio-selection argument selects symmetric $Z$ and
skew $Y$ with positive $S$ and ratios less than one. This remains
valid when some basis $S$-values are negative: if every positive-$S$
ratio exceeded the quotient of the sums, summing $T-cS$ would be
strictly positive, a contradiction (the nonpositive-$S$ terms are
nonnegative). Tensor products factor both quadratic forms. This is
the factored-direction proof preserved in the previous research pass.
'''
    descent=(ROOT/'descent/descent.tex').read_text(encoding='utf-8')
    (ROOT/'research.tex').write_text(PREFIX.replace('Tensor-stable extrema and quantitative flatness\\\\over the real and complex fields','Tensor stability, activation thresholds\\\\and limitations of dimension reduction')+core+quant+activation+setup+descent+BIB,encoding='utf-8',newline='\n')


def main():
    assemble()
    checkers=('check_trace.py','sharpen/check.py','exponents/check_exact.py',
              'exponents/check_complex.py','descent/check.py')
    for checker in checkers:
        subprocess.run([sys.executable,str(ROOT/checker)],cwd=ROOT,check=True)
    # Reuse this project's existing Apache-licensed, warning-checking compiler.
    spec=importlib.util.spec_from_file_location('prior_build',ROOT.parent/'round3/build.py')
    compiler=importlib.util.module_from_spec(spec);spec.loader.exec_module(compiler)
    compiler.ROOT=ROOT
    pages={}
    for name in ('tensor_trace.tex','research.tex','sharpen/activation.tex'):
        pages[name]=compiler.compile_one(ROOT/name)
    # The supplementary subquadratic source has two contextual bibliography items
    # without explicit cite commands; use its independently compiled PDF.
    assert (ROOT/'exponents/subquadratic_tensor.pdf').is_file()
    paths=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
           and '__pycache__' not in p.parts and p.suffix not in ('.aux','.log','.out')
           and p.name!='verification.json']
    record={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
            'checkersPassed':list(checkers),'typesettingChecksPassed':True,
            'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},
            'scope':{'hadamardConjectureProved':False,'complexOneCopyConjectureProved':False,
                     'noveltyEstablished':False,'leanFormalization':False,'gitCommits':False}}
    (ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Built fourth-pass papers:',pages)


if __name__=='__main__':main()
