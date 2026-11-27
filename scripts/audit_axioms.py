# SPDX-License-Identifier: Apache-2.0
"""Audit the actual axiom closure of every configured comparison group."""
from pathlib import Path
from datetime import datetime, timezone
import json
import re
import subprocess
from comparison_groups import load_groups, declaration_names
from run_local_comparator import check_source_inventory,digest
ROOT = Path(__file__).resolve().parents[1]

def main():
    groups = load_groups(ROOT)
    names = declaration_names(groups)
    if not names:
        raise SystemExit("No targets")
    modules = list(dict.fromkeys(group["config"]["solution_module"] for group in groups))
    audit = ROOT / ".lake/Audit.lean"
    audit.write_text("module\n" + "\n".join("import " + module for module in modules) + "\n" +
        "\n".join("#print axioms " + name for name in names) + "\n", encoding="utf-8")
    result = subprocess.run(["lake", "env", "lean", str(audit)], cwd=ROOT,
        capture_output=True, text=True, encoding="utf-8")
    (ROOT / ".lake/axioms.log").write_text(result.stdout + result.stderr, encoding="utf-8")
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    profiles = {name: [item.strip() for item in items.split(",") if item.strip()]
        for name, items in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout):
        profiles[name] = []
    if set(profiles) != set(names):
        raise SystemExit("Incomplete axiom audit coverage")
    if {axiom for profile in profiles.values() for axiom in profile} - {"propext", "Quot.sound", "Classical.choice"}:
        raise SystemExit("Nonstandard proof axioms")
    data = {"checkedAtUTC": datetime.now(timezone.utc).isoformat(), "status": "passed",
        "declarations": profiles,
        "comparisonGroups": [{"id": group["id"], "config": group["path"]} for group in groups],
        "scope": "Every configured comparison declaration; principal paper coverage is a separate gate."}
    snapshot = ROOT / "submission/proof-hashes.json"
    if snapshot.exists():
        hashes = json.loads(snapshot.read_text(encoding="utf-8"))
        try:
            check_source_inventory(hashes)
            current = all((ROOT/name).is_file() and digest(ROOT/name)==value for name,value in hashes.items())
        except SystemExit:
            current = False
        if current:
            data["proofHashes"] = hashes
    (ROOT / "submission/axioms.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(data, indent=2))

if __name__ == "__main__":
    main()
