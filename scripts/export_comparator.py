"""Export the configured statements and proofs with the pinned Lean exporter.

The exports are local diagnostics, not a sandboxed registry verification.
The primitive target list follows Lean 4.35.0 Lake/CLI/Check.lean.
"""
import argparse
import json
from comparison_groups import select_group
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--config", default="comparator.json")
args = parser.parse_args()
group = select_group(root, args.config)
config = group["config"]
primitives = ("Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble "
              "Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat "
              "List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam").split()
targets = (["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] + config["theorem_names"] +
           config["permitted_axioms"] + primitives + config.get("definition_names", []))
output = root / group["exportDirectory"]
output.mkdir(parents=True, exist_ok=True)
subprocess.run(["lake", "build", config["challenge_module"], config["solution_module"]], cwd=root, check=True)
# Check names before export: exporter panics may otherwise leave partial output.
for role in ("challenge", "solution"):
    preflight = output / (role + "-targets.lean")
    preflight.write_text(
        "import " + config[role + "_module"] + "\n" +
        "\n".join("#check @" + name for name in targets) + "\n",
        encoding="utf-8", newline="\n")
    with (output / (role + "-targets.log")).open("wb") as stream:
        subprocess.run(["lake", "env", "lean", str(preflight)], cwd=root,
                       stdout=stream, stderr=subprocess.STDOUT, check=True)
for role in ("challenge", "solution"):
    with (output / (role + ".ndjson")).open("wb") as stream:
        subprocess.run(["lake", "env", "leanexport", config[role + "_module"], "--", *targets],
                       cwd=root, stdout=stream, check=True)
    print(role, (output / (role + ".ndjson")).stat().st_size, "bytes", flush=True)
