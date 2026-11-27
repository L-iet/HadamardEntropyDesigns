# SPDX-License-Identifier: Apache-2.0
"""Reproduce constructive certificates and obstruction tests."""
from pathlib import Path
from datetime import datetime, timezone
import importlib.util, hashlib, json, subprocess, sys

ROOT=Path(__file__).resolve().parent
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def prefix(title):
    return module('style',ROOT.parent/'round9/build.py').PREFIX.replace(
        'Support rigidity, optimal atom exchange,\\\\and modular Hadamard-extension counts',title)
def assemble():
    parts={key:(ROOT/path).read_text(encoding='utf-8') for key,path in
           [('rounding','rounding/rounding.tex'),('weighing','weighing/weighing.tex'),
            ('spectral','spectral/spectral.tex'),('completion','phase_quantum/completion.tex')]}
    intro=r'''
\begin{abstract}
We examine constructive steps and obstructions in four Hadamard
formulations. An explicit dephasing algorithm rounds sufficiently
small fourth-power dispersion into an exact quaternary Hadamard
matrix, including a two-objective certificate for approximately
orthogonal inputs. Real zero-supported completion of a two-zero
weighing matrix is equivalent to sign completion, with at most six
sign solutions beyond order four. The spectral branch derives exact
entry-move formulas and finite traps, then lifts these obstructions
to arbitrarily large known Hadamard orders. A rank-two residual
projection links two-column complex completion to qubit geometry;
classical real completion then implies automatic quaternary completion
when only two columns are missing.
All-order existence and bibliographic priority remain unresolved.
\end{abstract}
The conjecture asks for a real sign matrix $H$ with $HH^T=nI_n$
at every positive order divisible by four. Local certificates below
are not assumed to be attainable at every such order.
'''
    end=r'''
\section{What the constructive results still need}
The phase-rounding criterion requires a starting matrix inside a
dimension-dependent basin. We have no all-order construction reaching
that basin. The low-codimension completion criteria require almost all
columns to have been constructed already. The weighing results preserve
specified entries and therefore solve a constrained completion task.
The spectral traps rule out a universal strict-descent algorithm based
only on one or two entry changes, but do not rule out larger moves,
temporary energy increases, or different objective functions.

The next constructive targets are an input-producing theorem for
phase rounding, a compatible all-order weighing construction, and
a global exchange operation with a proved escape mechanism.
No full-conjecture proof or previously unknown order is claimed.
No Lean edits, git commits, publication or submission were made.
\end{document}
'''
    (ROOT/'research.tex').write_text(prefix('Constructive phase rounding, completion geometry,\\\\and obstructions to greedy repair')+
        intro+''.join(parts[k] for k in ('rounding','weighing','spectral','completion'))+end,encoding='utf-8',newline='\n')
    (ROOT/'phase_rounding.tex').write_text(prefix('Constructive fourth-phase rounding\\\\from explicit correlation certificates')+
        parts['rounding']+'\n\\end{document}\n',encoding='utf-8',newline='\n')
def main():
    assemble()
    checkers=[x+'/check.py' for x in ('rounding','weighing','spectral','phase_quantum')]
    for checker in checkers:
        r=subprocess.run([sys.executable,str(ROOT/checker)],cwd=ROOT,check=True,capture_output=True,encoding='utf-8')
        folder=ROOT/'.build'/'checkers'/Path(checker).parent.name;folder.mkdir(parents=True,exist_ok=True)
        (folder/'output.txt').write_text(r.stdout+r.stderr,encoding='utf-8')
        print(checker,'passed',flush=True)
    compiler=module('compiler',ROOT.parent/'round3/build.py');compiler.ROOT=ROOT
    pages={name:compiler.compile_one(ROOT/name) for name in ('phase_rounding.tex','research.tex')}
    paths=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
           and '__pycache__' not in p.parts and p.suffix not in ('.aux','.log','.out')
           and p!=ROOT/'verification.json']
    record={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
            'checkersPassed':checkers,'typesettingChecksPassed':True,
            'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},
            'scope':{'hadamardConjectureProved':False,'unknownOrderConstructed':False,
                     'noveltyEstablished':False,'leanFormalization':False,'gitCommits':False}}
    (ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Built fourteenth-pass papers:',pages)
if __name__=='__main__':main()
