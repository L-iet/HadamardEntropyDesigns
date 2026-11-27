# SPDX-License-Identifier: Apache-2.0
"""Regression checks for complete, independent, local comparison-group coverage."""
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from comparison_groups import load_groups, select_group, declaration_names

class GroupsTest(unittest.TestCase):
    def setUp(self):
        self.temp = TemporaryDirectory(dir=Path(__file__).resolve().parent)
        self.root = Path(self.temp.name)
        (self.root / "submission").mkdir()
        self.config("comparator.json", "Challenge", "Solution")
    def tearDown(self):
        self.temp.cleanup()
    def config(self, name, challenge, solution):
        (self.root/name).write_text(json.dumps({"challenge_module":challenge,
            "solution_module":solution,"theorem_names":["Example.result"],
            "definition_names":["Example.object"]}),encoding="utf-8")
    def manifest(self, entries):
        (self.root/"submission/comparison-groups.json").write_text(
            json.dumps({"schemaVersion":1,"groups":entries}),encoding="utf-8")
    def test_legacy_main(self):
        g=load_groups(self.root)
        self.assertEqual(len(g),1)
        self.assertEqual(g[0]["localReport"],"submission/local-comparator-result.json")
    def test_two_independent_groups(self):
        self.config("comparator-algorithms.json","AlgorithmChallenge","AlgorithmSolution")
        self.manifest([{"id":"main","config":"comparator.json"},
            {"id":"algorithms","config":"comparator-algorithms.json"}])
        g=load_groups(self.root)
        self.assertEqual(len(g),2)
        self.assertNotEqual(g[0]["exportDirectory"],g[1]["exportDirectory"])
        self.assertEqual(select_group(self.root,"comparator-algorithms.json")["id"],"algorithms")
        self.assertEqual(declaration_names(g),["Example.result","Example.object"])
    def test_duplicate_group_rejected(self):
        self.manifest([{"id":"main","config":"comparator.json"}]*2)
        with self.assertRaises(ValueError):load_groups(self.root)
    def test_path_escape_rejected(self):
        self.manifest([{"id":"main","config":"../outside.json"}])
        with self.assertRaises(ValueError):load_groups(self.root)
    def test_proof_cannot_be_challenge(self):
        self.config("comparator-algorithms.json","Solution","AlgorithmSolution")
        self.manifest([{"id":"main","config":"comparator.json"},
            {"id":"algorithms","config":"comparator-algorithms.json"}])
        with self.assertRaises(ValueError):load_groups(self.root)
    def test_unknown_config_rejected(self):
        with self.assertRaises(ValueError):select_group(self.root,"not-registered.json")
    def test_missing_main_rejected(self):
        self.manifest([{"id":"algorithms","config":"comparator.json"}])
        with self.assertRaises(ValueError):load_groups(self.root)
    def test_missing_secondary_config_rejected(self):
        self.manifest([{"id":"main","config":"comparator.json"},
            {"id":"algorithms","config":"missing.json"}])
        with self.assertRaises(FileNotFoundError):load_groups(self.root)

    def test_paper_entry_with_relocated_development_config(self):
        self.config("comparator.json","PaperChallenge","PaperSolution")
        (self.root/"configs/development").mkdir(parents=True)
        path="configs/development/comparator-main.json"
        self.config(path,"Challenge","Solution")
        self.manifest([{"id":"main","config":"comparator.json"},
            {"id":"development-main","config":path}])
        self.assertEqual(select_group(self.root,"comparator.json")["config"]["challenge_module"],"PaperChallenge")
        self.assertEqual(select_group(self.root,path)["id"],"development-main")

if __name__=="__main__":unittest.main()
