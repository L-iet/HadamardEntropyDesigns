# SPDX-License-Identifier: Apache-2.0
"""Reproduce the fifteenth bounded research pass."""
from pathlib import Path
from datetime import datetime,timezone
import importlib.util,hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parent
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def prefix(title):
    return module('style',ROOT.parent/'round9/build.py').PREFIX.replace(
      'Support rigidity, optimal atom exchange,\\\\and modular Hadamard-extension counts',title).replace(
      r'\begin{document}',r'\setcounter{MaxMatrixCols}{20}'+'\n'+r'\begin{document}')
def assemble():
    parts={k:(ROOT/k/'main.tex').read_text(encoding='utf-8') for k in ('phase','completion','exchanges','weighing')}
    intro=r'''
\begin{abstract}
Every real sign matrix that is not Hadamard is a strict saddle of
the complex-phase squared-Gram energy. An exact construction supplies
integer phase directions, escaping even the previously certified
discrete one- and two-entry traps. Separately, classical real completion
theory yields quaternary completion with at most three columns missing,
with a bounded candidate enumeration algorithm. We also examine
larger discrete exchanges and support-preserving weighing moves.
These results provide escape and completion tools; they do not produce
the required inputs at every admissible order or prove the conjecture.
Bibliographic priority is unestablished.
\end{abstract}
The real Hadamard conjecture asks for a sign matrix $H$ satisfying
$HH^T=nI$ at every positive order divisible by four.
Moving into complex phases changes the feasible set; returning to a
finite phase alphabet is an additional requirement throughout this report.
'''
    end=r'''
\section{The remaining construction problem}
Continuous phase escape is available at every non-Hadamard real sign
matrix, but a phase trajectory can approach a complex Hadamard matrix
outside the four-phase alphabet. No theorem makes phase dispersion
decrease along the new direction. The completion algorithm needs all
but a bounded number of columns in advance, and weighing exchanges
must preserve both their algebraic equations and their zero support.
None of these hypotheses is supplied uniformly at unknown orders.
The next target is an operation coupling orthogonality improvement to
phase quantization, or an input-producing theorem for the bounded
completion algorithm. No Lean edits, git commits or submissions were made.
\end{document}
'''
    (ROOT/'research.tex').write_text(prefix('Continuous phase escape, bounded completion,\\\\and larger discrete exchanges')+
        intro+''.join(parts[k] for k in ('phase','completion','exchanges','weighing'))+end,encoding='utf-8',newline='\n')
    (ROOT/'phase_escape.tex').write_text(prefix('Exact phase escape from every\\\\non-Hadamard real sign matrix')+
        parts['phase']+'\n\\end{document}\n',encoding='utf-8',newline='\n')
def main():
    assemble()
    checkers=[x+'/check.py' for x in ('phase','completion','exchanges','weighing')]
    for checker in checkers:
        r=subprocess.run([sys.executable,str(ROOT/checker)],cwd=ROOT,check=True,capture_output=True,encoding='utf-8')
        folder=ROOT/'.build'/'checkers'/Path(checker).parent.name;folder.mkdir(parents=True,exist_ok=True)
        (folder/'output.txt').write_text(r.stdout+r.stderr,encoding='utf-8')
        print(checker,'passed',flush=True)
    compiler=module('compiler',ROOT.parent/'round3/build.py');compiler.ROOT=ROOT
    pages={name:compiler.compile_one(ROOT/name) for name in ('phase_escape.tex','research.tex')}
    paths=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts and '__pycache__' not in p.parts
           and p.suffix not in ('.aux','.log','.out') and p!=ROOT/'verification.json']
    rec={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,'checkersPassed':checkers,
         'typesettingChecksPassed':True,'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},
         'scope':{'hadamardConjectureProved':False,'unknownOrderConstructed':False,'noveltyEstablished':False,
                  'leanFormalization':False,'gitCommits':False}}
    (ROOT/'verification.json').write_text(json.dumps(rec,indent=2)+'\n',encoding='utf-8')
    print('Built fifteenth-pass papers:',pages)
if __name__=='__main__':main()
