# SPDX-License-Identifier: Apache-2.0
"""Static paper-entry provenance and size checks; does not execute Lean."""
from pathlib import Path
import hashlib,json,re
from check_submission import code_only

ROOT=Path(__file__).resolve().parents[1]

def main():
    record=json.loads((ROOT/'submission/PAPER_ENTRY.json').read_text(encoding='utf-8'))
    config=json.loads((ROOT/record['configuration']).read_text(encoding='utf-8'))
    paper=(ROOT/record['challenge']).read_text(encoding='utf-8')
    errors=[]
    if len(paper.encode())>102400 or len(paper.splitlines())>1000:errors.append('Paper Challenge exceeds a hard size limit')
    if config['challenge_module']!='PaperChallenge' or config['solution_module']!='PaperSolution':errors.append('Unexpected paper module names')
    if set(config['permitted_axioms'])!={'propext','Quot.sound','Classical.choice'}:errors.append('Unexpected permitted axioms')
    actual=set(config['theorem_names'])
    expected=set(record['headlineTheoremNames']+record['supportingTheoremNames'])
    if actual!=expected:errors.append('Paper theorem selection differs from source map')
    if config['definition_names']!=record['concreteDefinitionNames']:errors.append('Paper definition selection differs from source map')
    for item in record['sourceMap']:
        source=ROOT/item['originalFile']
        if not source.resolve().is_relative_to(ROOT.resolve()):errors.append('Nonlocal provenance source');continue
        lines=source.read_text(encoding='utf-8').splitlines(keepends=True)
        original=''.join(lines[item['originalStartLine']-1:item['originalEndLine']]).rstrip()+'\n'
        if hashlib.sha256(original.encode()).hexdigest()!=item['originalDeclarationSHA256']:
            errors.append('Original declaration changed: '+item['name'])
        if original not in paper:errors.append('Copied declaration text differs: '+item['name'])
    imports=re.findall(r'^public import (\S+)',code_only(paper),re.M)
    if any(m.split('.')[0] not in {'Mathlib','Lean','Init','Std'} for m in imports):errors.append('Project-specific Challenge import')
    solution=code_only((ROOT/record['solution']).read_text(encoding='utf-8'))
    imports=re.findall(r'^public import (\S+)',solution,re.M)
    if imports!=['Solution','SequenceSolution','PrimeExponentSolution']:errors.append('Unexpected proof imports')
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b|Lean\.ofReduceBool',solution):errors.append('New solution contains a proof escape')
    if record['locallyCompiled'] or record['locallyCompared'] or record['localKernelChecksRun']:errors.append('Static packaging must not claim local proof verification')
    print(json.dumps({'status':'failed' if errors else 'passed static checks only',
        'challengeBytes':len(paper.encode()),'challengeLines':len(paper.splitlines()),
        'copiedDeclarations':len(record['sourceMap']),'localLeanExecuted':False,'errors':errors},indent=2))
    return 1 if errors else 0

if __name__=='__main__':raise SystemExit(main())
