# SPDX-License-Identifier: Apache-2.0
"""Run the selected sandboxed Comparator entry; optionally check all development groups."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import json
import subprocess
from comparison_groups import load_groups, select_group
from run_local_comparator import check_source_inventory, digest
ROOT = Path(__file__).resolve().parents[1]

def check_snapshot(hashes):
    check_source_inventory(hashes)
    for name, expected in hashes.items():
        if digest(ROOT / name) != expected:
            raise SystemExit("Rebuild and audit changed source before comparison: " + name)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", default="comparator.json")
    parser.add_argument("--all-groups", action="store_true")
    args = parser.parse_args()
    proof = ROOT / "submission/proof-hashes.json"
    if not proof.exists():
        raise SystemExit("Record verified source hashes before comparison")
    hashes = json.loads(proof.read_text(encoding="utf-8"))
    check_snapshot(hashes)
    for group in (load_groups(ROOT) if args.all_groups else [select_group(ROOT, args.config)]):
        result = subprocess.run(["lake", "comparator", "--config", group["path"]], cwd=ROOT,
            capture_output=True, text=True, encoding="utf-8", errors="replace")
        log = result.stdout + result.stderr
        suffix = "" if group["id"] == "main" else "-" + group["id"]
        (ROOT / (".lake/comparator" + suffix + ".log")).write_text(log, encoding="utf-8")
        lean = "Lean default kernel accepts the solution" in log
        nanoda = "nanoda kernel accepts the solution" in log
        passed = result.returncode == 0 and lean and nanoda
        if passed:
            check_snapshot(hashes)
        config = group["config"]
        data = {"status": "passed" if passed else "failed", "exitCode": result.returncode,
            "checkedAtUTC": datetime.now(timezone.utc).isoformat(), "proofHashes": hashes,
            "comparisonGroup": group["id"], "configPath": group["path"],
            "theoremNames": config["theorem_names"], "definitionNames": config.get("definition_names", []),
            "leanKernelAccepted": lean, "nanodaAccepted": nanoda, "sandboxedSourceBuild": True,
            "notRegistryVerification": True,
            "scope": "This bounded comparison group; every registered group and paper coverage are separate gates."}
        (ROOT / group["sandboxReport"]).write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        print(log, flush=True)
        if not passed:
            raise SystemExit(result.returncode or "Missing explicit acceptance by both independent kernels")

if __name__ == "__main__":
    main()
