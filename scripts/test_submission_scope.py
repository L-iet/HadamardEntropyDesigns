# SPDX-License-Identifier: Apache-2.0
"""Check theorem coverage independently of README or disclosure wording."""
from pathlib import Path
from tempfile import TemporaryDirectory
import json,shutil,unittest
from submission_scope import validate
ROOT=Path(__file__).resolve().parents[1]
class ScopeTest(unittest.TestCase):
    def setUp(self):
        self.parent=ROOT/'.lake';self.parent.mkdir(exist_ok=True)
        self.temp=TemporaryDirectory(dir=self.parent)
        self.root=Path(self.temp.name)
        assert self.root.resolve().is_relative_to(self.parent.resolve())
        for relative in ['paper','submission']:(self.root/relative).mkdir()
        self.put('comparator.json',{'theorem_names':['Example.proved']})
        self.put('paper/ALIGNMENT.json',{'claims':[
            {'id':'A','status':'proved','declaration':'Example.proved'},
            {'id':'B','status':'pending','declaration':None}]})
        self.put('submission/SCOPE.json',{'mode':'configured-verified-results','principalClaimCount':2,
            'submittedPrincipalClaims':[{'id':'A'}],'unsubmittedPrincipalClaims':[{'id':'B'}],
            'comparatorConfigurations':['comparator.json'],'proofCoverageComplete':False,
            'registryVerificationClaimed':False})
        self.put('formalization.yaml',{'project':{'description':'Verified submission scope: A'},'limitations':['B pending']})
        (self.root/'README.md').write_text('[technical guide](TECHNICAL.md)',encoding='utf-8')
        (self.root/'TECHNICAL.md').write_text('B pending',encoding='utf-8')
        (self.root/'paper/main.tex').write_text('\\input{formalization-status}',encoding='utf-8')
        (self.root/'paper/formalization-status.tex').write_text('B pending',encoding='utf-8')
    def tearDown(self):self.temp.cleanup()
    def put(self,name,data):(self.root/name).write_text(json.dumps(data),encoding='utf-8')
    def mutate(self,key,value):
        file=self.root/'submission/SCOPE.json';data=json.loads(file.read_text());data[key]=value;self.put('submission/SCOPE.json',data)
    def errors(self):return validate(self.root)[2]
    def test_explicit_partial_scope_allowed(self):self.assertEqual(self.errors(),[])
    def test_mismatched_excluded_inventory_rejected(self):
        self.mutate('unsubmittedPrincipalClaims',[])
        self.assertTrue(any('Unsubmitted' in e for e in self.errors()))
    def test_whole_paper_overclaim_rejected(self):
        self.mutate('proofCoverageComplete',True)
        self.assertTrue(any('Whole-paper' in e for e in self.errors()))
    def test_unsupported_claim_inclusion_rejected(self):
        self.mutate('submittedPrincipalClaims',[{'id':'A'},{'id':'B'}])
        self.assertTrue(any('Submitted' in e for e in self.errors()))
    def test_documentation_wording_is_not_a_gate(self):
        for name in ['README.md','TECHNICAL.md','paper/main.tex','paper/formalization-status.tex','formalization.yaml']:
            (self.root/name).unlink()
        self.assertEqual(self.errors(),[])
if __name__=='__main__':unittest.main()
