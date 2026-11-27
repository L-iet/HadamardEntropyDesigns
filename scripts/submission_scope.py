# SPDX-License-Identifier: Apache-2.0
"""Validate explicit verified-subset scope; no proof or kernel requirement is waived."""
from pathlib import Path
import json
GOOD={'formalized','proved','verified'}
def groups(root):
    root=Path(root);manifest=root/'submission/comparison-groups.json'
    rows=json.loads(manifest.read_text(encoding='utf-8'))['groups'] if manifest.exists() else [{'id':'main','config':'comparator.json'}]
    result=[]
    for row in rows:
        suffix='' if row['id']=='main' else '-'+row['id']
        result.append({'id':row['id'],'path':row['config'],
            'config':json.loads((root/row['config']).read_text(encoding='utf-8')),
            'localReport':'submission/local-comparator'+suffix+'-result.json',
            'sandboxReport':'submission/comparator'+suffix+'-result.json',
            'exportDirectory':'.lake/final-exports'+suffix})
    return result
def validate(root):
    root=Path(root);errors=[]
    scope=json.loads((root/'submission/SCOPE.json').read_text(encoding='utf-8'))
    alignment=json.loads((root/'paper/ALIGNMENT.json').read_text(encoding='utf-8'))
    claims=next(alignment[k] for k in ['principalClaims','principal_claims','claims'] if k in alignment)
    configurations=groups(root)
    targets={n for group in configurations for n in group['config']['theorem_names']}
    expected=[];pending=[]
    for c in claims:
        status=c.get('leanStatus',c.get('lean_status',c.get('status','pending')))
        names=c.get('leanDeclarations',c.get('lean_declarations',[]))
        if not names:
            name=c.get('declaration',c.get('lean_declaration'));names=[name] if name else []
        (expected if status in GOOD and names and all(n in targets for n in names) else pending).append(c['id'])
    included=[c['id'] for c in scope['submittedPrincipalClaims']]
    excluded=[c['id'] for c in scope['unsubmittedPrincipalClaims']]
    if len(included)!=len(set(included)) or sorted(included)!=sorted(expected):errors.append('Submitted principal claim scope mismatch')
    if len(excluded)!=len(set(excluded)) or sorted(excluded)!=sorted(pending):errors.append('Unsubmitted principal claim scope mismatch')
    if scope.get('principalClaimCount')!=len(claims):errors.append('Principal claim count mismatch')
    if sorted(scope.get('comparatorConfigurations',[]))!=sorted(g['path'] for g in configurations):errors.append('Comparison configuration scope mismatch')
    if scope.get('mode')!='configured-verified-results':errors.append('Missing explicit verified-results scope')
    if scope.get('proofCoverageComplete')!=(not pending):errors.append('Whole-paper coverage incorrectly claimed')
    if scope.get('registryVerificationClaimed') is not False:errors.append('Registry verification must not be inferred from local preparation')
    paper=(root/'paper/formalization-status.tex').read_text(encoding='utf-8')
    main=(root/'paper/main.tex').read_text(encoding='utf-8')
    readme=(root/'README.txt').read_text(encoding='utf-8')
    metadata=json.loads((root/'formalization.yaml').read_text(encoding='utf-8'))
    limitations=' '.join(metadata.get('limitations',[]))
    for claim in pending:
        if any(claim not in text for text in [paper,readme,limitations]):errors.append('Missing gap disclosure: '+claim)
    if '\\input{formalization-status}' not in main:errors.append('Paper does not include formalization scope')
    if not metadata['project']['description'].startswith('Verified submission scope:'):errors.append('Registry abstract does not state limited scope')
    return scope,configurations,errors
