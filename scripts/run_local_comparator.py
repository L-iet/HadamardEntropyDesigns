# SPDX-License-Identifier: Apache-2.0
"""Check fresh exports locally, explicitly without source-build sandboxing."""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
from comparison_groups import select_group
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def check_source_inventory(hashes):
    sources = set()
    for directory, children, files in os.walk(ROOT):
        children[:] = [name for name in children if name not in {
            ".git", ".lake", ".proof-tools", "artifacts", "__pycache__", ".build"}]
        sources.update((Path(directory) / name).relative_to(ROOT).as_posix()
                       for name in files if name.endswith(".lean"))
    recorded = {name for name in hashes if name.endswith(".lean")}
    if sources != recorded:
        raise SystemExit("Rebuild/audit and refresh source inventory first: "
                         + ", ".join(sorted(sources ^ recorded)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", default="comparator.json")
    args = parser.parse_args()
    group = select_group(ROOT, args.config)
    suffix = "" if group["id"] == "main" else "-" + group["id"]
    exports = ROOT / group["exportDirectory"]
    hashes = json.loads((ROOT / "submission/proof-hashes.json").read_text(encoding="utf-8"))
    check_source_inventory(hashes)
    for name, expected in hashes.items():
        if digest(ROOT / name) != expected:
            raise SystemExit("Rebuild/audit and refresh proof hashes first: " + name)
    subprocess.run([sys.executable, "scripts/export_comparator.py", "--config", group["path"]], cwd=ROOT, check=True)
    config = group["config"]
    env = os.environ.copy()
    config_path = ROOT / group["path"]
    adaptation = None
    if os.name == "nt":
        # Lake 4.35's unsandboxed diagnostic invokes Unix 'which' and a bare
        # nanoda_bin. Supply Git's existing which and the bundled Windows exe.
        git = shutil.which("git")
        if not git:
            raise SystemExit("Git is required for Lake's executable discovery.")
        git_usr = Path(git).resolve().parents[1] / "usr/bin"
        if (git_usr / "which.exe").is_file():
            env["PATH"] = str(git_usr) + os.pathsep + env["PATH"]
        prefix = subprocess.check_output(
            ["lake", "env", "lean", "--print-prefix"], cwd=ROOT, text=True).strip()
        checker = Path(prefix) / "bin/nanoda_bin.exe"
        if not checker.is_file():
            raise SystemExit("The pinned Windows toolchain has no NanoDa checker.")
        adapted = dict(config)
        adapted["enable_nanoda"] = False
        adapted["external_kernels"] = {"nanoda": [checker.as_posix()]}
        config_path = ROOT / (".lake/local-comparator-windows" + suffix + ".json")
        config_path.write_text(json.dumps(adapted, indent=2) + "\n", encoding="utf-8")
        adaptation = "Windows runtime only: explicit bundled nanoda_bin.exe path."
    command = [
        "lake", "env", "lake", "comparator", "--config", str(config_path),
        "--challenge-from-export", group["exportDirectory"] + "/challenge.ndjson",
        "--solution-from-export", group["exportDirectory"] + "/solution.ndjson",
        "--inadvisably-no-sandbox",
    ]
    # Persist each line immediately: a terminated host must not erase the
    # evidence already produced by a long independent kernel check.
    chunks = []
    with (ROOT / (".lake/local-comparator" + suffix + ".log")).open("w", encoding="utf-8") as output:
        process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True,
                                   encoding="utf-8", errors="replace", bufsize=1)
        assert process.stdout is not None
        for line in process.stdout:
            chunks.append(line)
            output.write(line)
            output.flush()
            os.fsync(output.fileno())
            print(line, end="", flush=True)
        returncode = process.wait()
    log = "".join(chunks)
    if returncode:
        raise SystemExit(returncode)
    if "Lean default kernel accepts the solution" not in log or "nanoda kernel accepts the solution" not in log:
        raise SystemExit("Missing explicit independent kernel acceptance messages.")
    check_source_inventory(hashes)
    for name, expected in hashes.items():
        if digest(ROOT / name) != expected:
            raise SystemExit("Sources changed during comparison: " + name)
    report = {
        "checkedAtUTC": datetime.now(timezone.utc).isoformat(),
        "status": "passed",
        "mode": "local exported-proof diagnostic",
        "comparisonGroup": group["id"],
        "configPath": group["path"],
        "sandboxedSourceBuild": False,
        "notRegistryVerification": True,
        "leanKernelAccepted": True,
        "nanodaAccepted": True,
        "theoremNames": config["theorem_names"],
        "definitionNames": config.get("definition_names", []),
        "proofHashes": hashes,
        "exports": {role: hashlib.sha256(
            (exports / (role + ".ndjson")).read_bytes()).hexdigest()
            for role in ("challenge", "solution")},
        "runtimeAdaptation": adaptation,
        "evidence": "Observed Comparator exit 0 and explicit Lean and NanoDa acceptance; not a registry report.",
    }
    (ROOT / group["localReport"]).write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
