# SPDX-License-Identifier: Apache-2.0
"""Fast local Lean preflight. Independent/registry kernel checks are not claimed.
The strict check_submission.py --ready gate is intentionally unchanged.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,sys
try:
 from comparison_groups import load_groups,declaration_names
except ModuleNotFoundError as exc:
 if exc.name!='comparison_groups':raise
 def load_groups(path):
  config=json.loads((path/'comparator.json').read_text(encoding='utf-8'))
  return [{'id':'main','config':config}]
 def declaration_names(groups):
  return list(dict.fromkeys(name for g in groups for name in
   g['config']['theorem_names']+g['config'].get('definition_names',[])))
ROOT=Path(__file__).resolve().parents[1]
read=lambda f:json.loads(f.read_text(encoding='utf-8'))
canonical=lambda f:hashlib.sha256(f.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def main():
 errors=[]
 process=subprocess.run([sys.executable,str(ROOT/'scripts/check_submission.py')],cwd=ROOT,
  stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
 try:structure=json.loads(process.stdout)
 except (ValueError,TypeError):
  print(process.stdout);return 1
 errors.extend(structure.get('errors',[]))
 if process.returncode and not errors:errors.append('Structural check failed')
 hashes=read(ROOT/'submission/proof-hashes.json')
 for name,h in hashes.items():
  if not (ROOT/name).is_file() or canonical(ROOT/name)!=h:errors.append('Source snapshot mismatch: '+name)
 groups=load_groups(ROOT);expected=set(declaration_names(groups))
 build=read(ROOT/'submission/build.json');audit=read(ROOT/'submission/axioms.json')
 if build.get('status')!='passed' or build.get('proofHashes')!=hashes:errors.append('Current full Lean build is missing')
 if audit.get('status')!='passed' or audit.get('proofHashes')!=hashes:errors.append('Current axiom audit is missing')
 profiles=audit.get('declarations',{})
 if set(profiles)!=expected:errors.append('Axiom audit target coverage mismatch')
 allowed={'propext','Classical.choice','Quot.sound'}
 for name,axioms in profiles.items():
  if set(axioms)-allowed:errors.append('Additional axioms in '+name+': '+', '.join(sorted(set(axioms)-allowed)))
 record=read(ROOT/'paper/ALIGNMENT.json')
 principal=next(record[k] for k in ('principalClaims','principal_claims','claims') if k in record)
 pending=[]
 for claim in principal:
  status=claim.get('leanStatus',claim.get('lean_status',claim.get('status','pending')))
  declarations=claim.get('leanDeclarations',claim.get('lean_declarations',[]))
  if not declarations:
   declaration=claim.get('declaration',claim.get('lean_declaration'))
   declarations=[declaration] if declaration else []
  if status not in ('formalized','proved','verified') or not declarations or any(n not in expected for n in declarations):
   pending.append(claim.get('id',claim.get('title','unnamed')))
 paper=read(ROOT/'submission/paper.json')
 if not paper.get('typesettingChecksPassed'):errors.append('Paper typesetting checks are missing')
 for name,h in paper.get('sourceHashes',{}).items():
  if not (ROOT/'paper'/name).is_file() or canonical(ROOT/'paper'/name)!=h:errors.append('Paper source snapshot mismatch: '+name)
 pdf=ROOT/'paper/main.pdf'
 if not pdf.is_file() or hashlib.sha256(pdf.read_bytes()).hexdigest()!=paper.get('pdfSHA256'):errors.append('Paper PDF snapshot mismatch')
 report={'status':'passed' if not errors else 'failed','checkedAtUTC':datetime.now(timezone.utc).isoformat(),
  'mode':'ordinary Lean build, complete target axiom audit and local submission preflight',
  'errors':errors,'proofHashes':hashes,'comparisonGroups':[g['id'] for g in groups],
  'auditedDeclarations':len(profiles),'permittedAxioms':sorted(allowed),
  'pendingPrincipalClaims':pending,'provedPrincipalClaims':len(principal)-len(pending),'totalPrincipalClaims':len(principal),
  'leanProofCoverageComplete':not pending,
  'independentKernelChecks':'deferred in this preflight; historical receipts are retained separately',
  'sandboxedSourceBuild':False,'notRegistryVerification':True,
  'strictReadinessGateUnchanged':True,'paperPDFSHA256':paper.get('pdfSHA256')}
 out=ROOT/'submission/lean-preflight.json';out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
 print(json.dumps({k:v for k,v in report.items() if k!='proofHashes'},indent=2))
 return 1 if errors else 0
if __name__=='__main__':raise SystemExit(main())
