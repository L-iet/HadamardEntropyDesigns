# SPDX-License-Identifier: Apache-2.0
"""Regression checks that secondary specifications cannot escape source/readiness gates."""
from contextlib import redirect_stdout
from io import StringIO
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch
PROJECT = next(parent for parent in Path(__file__).resolve().parents if (parent/'lean-toolchain').is_file())
sys.path.append(str(PROJECT/'scripts'))
import check_submission as scanner

class CoverageTest(unittest.TestCase):
    def setUp(self):
        (PROJECT/'.lake').mkdir(parents=True, exist_ok=True)
        self.temp=TemporaryDirectory(dir=PROJECT/'.lake')
        self.root=Path(self.temp.name)
        assert self.root.resolve().is_relative_to((PROJECT/'.lake').resolve())
        (self.root/'paper').mkdir();(self.root/'submission').mkdir()
        for name in ('lean-toolchain','lakefile.toml','LICENSE','paper/main.tex'):
            self.write(name,'fixture')
        self.write('lake-manifest.json',json.dumps({'packages':[]}))
        self.write('formalization.yaml',json.dumps({'project':{
            'name':'Fixture','description':'Scanner test only','authors':['Test'],
            'responsible_maintainers':['Test'],'license':'Apache-2.0'}}))
        self.write('paper/ALIGNMENT.json',json.dumps({'principal_claims':[
            {'id':'MAIN','lean_status':'proved','lean_declaration':'Example.main'},
            {'id':'ALGORITHM','lean_status':'proved','lean_declaration':'Example.algorithm'}]}))
        for name,challenge,solution,target in [
            ('comparator.json','Challenge','Solution','Example.main'),
            ('comparator-algorithms.json','AlgorithmChallenge','AlgorithmSolution','Example.algorithm')]:
            self.write(name,json.dumps({'challenge_module':challenge,'solution_module':solution,
                'theorem_names':[target],'definition_names':[],
                'permitted_axioms':['propext','Classical.choice','Quot.sound']}))
            short=target.split('.')[-1]
            self.write(challenge+'.lean','module\npublic import Mathlib\nnamespace Example\n'
                +'theorem '+short+' : True := by sorry\nend Example\n')
            self.write(solution+'.lean','module\nnamespace Example\n'
                +'theorem '+short+' : True := by trivial\nend Example\n')
        self.write('submission/comparison-groups.json',json.dumps({'schemaVersion':1,'groups':[
            {'id':'main','config':'comparator.json'},
            {'id':'algorithms','config':'comparator-algorithms.json'}]}))
    def tearDown(self):self.temp.cleanup()
    def write(self,name,text):(self.root/name).write_text(text,encoding='utf-8')
    def run_check(self,ready=False):
        stream=StringIO()
        argv=['check_submission.py']+(['--ready'] if ready else [])
        with patch.object(scanner,'ROOT',self.root),patch.object(scanner,'check_baseline_provenance',lambda:[]),patch.object(sys,'argv',argv),redirect_stdout(stream):
            code=scanner.main()
        return code,json.loads(stream.getvalue())
    def test_valid_groups_and_specification_holes(self):
        code,report=self.run_check()
        self.assertEqual(code,0);self.assertEqual(report['errors'],[])
        self.assertEqual(report['intentionalChallengePlaceholders'],2)
        self.assertFalse(report['ready'])
    def test_secondary_solution_hole_rejected(self):
        self.write('AlgorithmSolution.lean','module\ntheorem bad : False := by sorry\n')
        code,report=self.run_check()
        self.assertEqual(code,1);self.assertTrue(any('AlgorithmSolution.lean' in e and 'Forbidden' in e for e in report['errors']))
    def test_secondary_challenge_import_in_proof_rejected(self):
        self.write('AlgorithmSolution.lean','module\npublic import AlgorithmChallenge\n')
        code,report=self.run_check()
        self.assertEqual(code,1);self.assertTrue(any('Proof imports independent Challenge' in e for e in report['errors']))
    def test_secondary_challenge_size_rejected(self):
        self.write('AlgorithmChallenge.lean','module\n'+'\n'*1001)
        code,report=self.run_check()
        self.assertEqual(code,1);self.assertTrue(any('Oversized independent Challenge: AlgorithmChallenge.lean' in e for e in report['errors']))
    def test_unregistered_challenge_holes_rejected(self):
        self.write('UnregisteredChallenge.lean','module\ntheorem bad : False := by sorry\n')
        code,report=self.run_check()
        self.assertEqual(code,1);self.assertTrue(any('Forbidden' in e and 'UnregisteredChallenge.lean' in e for e in report['errors']))
    def test_principal_target_must_exist_in_some_group(self):
        self.write('comparator-algorithms.json',json.dumps({'challenge_module':'AlgorithmChallenge',
            'solution_module':'AlgorithmSolution','theorem_names':['Example.other'],'permitted_axioms':[]}))
        _,report=self.run_check()
        self.assertIn('ALGORITHM: missing comparison target',report['pendingPrincipalClaims'])
    def test_lookalike_canonical_import_rejected(self):
        self.write('AlgorithmChallenge.lean','module\npublic import MathlibPretend\n')
        code,report=self.run_check()
        self.assertEqual(code,1);self.assertTrue(any('Noncanonical' in e and 'MathlibPretend' in e for e in report['errors']))
    def test_secondary_report_required_for_readiness(self):
        code,report=self.run_check(ready=True)
        self.assertEqual(code,1)
        self.assertIn('Missing verification artifact submission/comparator-algorithms-result.json',report['errors'])

if __name__=='__main__':unittest.main()
