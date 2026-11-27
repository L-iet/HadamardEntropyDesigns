# SPDX-License-Identifier: Apache-2.0
"""Check that source inventory and license tampering fail the provenance gate."""
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch
import check_baseline_provenance as provenance

PROJECT = Path(__file__).resolve().parents[1]


class ProvenanceTest(unittest.TestCase):
    def setUp(self):
        (PROJECT / ".lake").mkdir(parents=True, exist_ok=True)
        self.temp = TemporaryDirectory(dir=PROJECT / ".lake")
        self.root = Path(self.temp.name)
        assert self.root.resolve().is_relative_to((PROJECT / ".lake").resolve())
        (self.root / "EntropyDesigns").mkdir()
        (self.root / "submission").mkdir()
        (self.root / "LICENSE").write_text("Apache-2.0 test fixture\n", encoding="utf-8")
        for name in ("EntropyDesigns.lean", "Solution.lean", "CofiniteSolution.lean",
                     "EntropyDesigns/Example.lean"):
            (self.root / name).write_text("module\n", encoding="utf-8")
        record = {"license": "Apache-2.0", "licenseFile": "LICENSE",
                  "licenseCanonicalLFSHA256": provenance.canonical_digest(self.root / "LICENSE"),
                  "sourceFiles": [{"file": name, "canonicalLFSHA256":
                                   provenance.canonical_digest(self.root / name)}
                                  for name in sorted(provenance.construction_sources(self.root))]}
        (self.root / "submission/construction-source-provenance.json").write_text(
            json.dumps(record), encoding="utf-8")

    def tearDown(self):
        self.temp.cleanup()

    def check(self):
        with patch.object(provenance, "ROOT", self.root):
            return provenance.check_baseline_provenance()

    def test_valid_inventory(self):
        self.assertEqual(self.check(), [])

    def test_changed_proof_rejected(self):
        (self.root / "EntropyDesigns/Example.lean").write_text("module\n-- changed\n", encoding="utf-8")
        self.assertTrue(any("differs from licensed provenance" in error for error in self.check()))

    def test_unrecorded_source_rejected(self):
        (self.root / "EntropyDesigns/Extra.lean").write_text("module\n", encoding="utf-8")
        self.assertTrue(any("inventory differs" in error for error in self.check()))

    def test_changed_license_rejected(self):
        (self.root / "LICENSE").write_text("changed\n", encoding="utf-8")
        self.assertTrue(any("license text changed" in error for error in self.check()))

    def test_missing_manifest_rejected(self):
        (self.root / "submission/construction-source-provenance.json").unlink()
        self.assertTrue(any("Invalid construction source provenance" in error for error in self.check()))

    def test_missing_imported_construction_attribution_rejected(self):
        (self.root / "HadamardMultibase").mkdir()
        self.assertTrue(any("Missing licensed construction attribution" in error for error in self.check()))

    def test_changed_recorded_attribution_rejected(self):
        (self.root / "licenses").mkdir()
        notice = self.root / "licenses/original-NOTICE.txt"
        notice.write_text("Original author's attribution\n", encoding="utf-8")
        manifest = self.root / "submission/construction-source-provenance.json"
        record = json.loads(manifest.read_text(encoding="utf-8"))
        record["attributionFiles"] = [{"file": "licenses/original-NOTICE.txt",
                                      "canonicalLFSHA256": provenance.canonical_digest(notice)}]
        manifest.write_text(json.dumps(record), encoding="utf-8")
        self.assertEqual(self.check(), [])
        notice.write_text("Changed attribution\n", encoding="utf-8")
        self.assertTrue(any("attribution file changed or missing" in error for error in self.check()))


if __name__ == "__main__":
    unittest.main()
