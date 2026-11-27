# SPDX-License-Identifier: Apache-2.0
"""Read every bounded independent comparison group, without silent fallbacks."""
from pathlib import Path
import json
import re


def load_groups(root):
    root = Path(root).resolve()
    manifest = root / "submission/comparison-groups.json"
    if manifest.exists():
        data = json.loads(manifest.read_text(encoding="utf-8"))
        if data.get("schemaVersion") != 1 or not isinstance(data.get("groups"), list):
            raise ValueError("Invalid comparison-group manifest")
        entries = data["groups"]
    else:
        entries = [{"id": "main", "config": "comparator.json"}]
    if not entries:
        raise ValueError("No comparison groups")
    groups = []
    identifiers, configs, challenges, solutions = set(), set(), set(), set()
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"id", "config"}:
            raise ValueError("Comparison groups require exactly id and config")
        label, name = entry["id"], entry["config"]
        if not isinstance(label, str) or not re.fullmatch(r"[a-z][a-z0-9-]*", label):
            raise ValueError("Invalid comparison group id")
        if label in identifiers:
            raise ValueError("Duplicate comparison group id: " + label)
        if not isinstance(name, str):
            raise ValueError("Comparison config must be a local JSON path")
        relative = Path(name)
        path = (root / relative).resolve()
        if relative.is_absolute() or ".." in relative.parts or relative.suffix != ".json" or not path.is_relative_to(root):
            raise ValueError("Comparison config escapes the project or is not JSON")
        if path in configs:
            raise ValueError("Duplicate comparison config")
        config = json.loads(path.read_text(encoding="utf-8"))
        for role in ("challenge", "solution"):
            module = config.get(role + "_module")
            if not isinstance(module, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", module):
                raise ValueError("Invalid " + role + " module in " + name)
        challenge, solution = config["challenge_module"], config["solution_module"]
        if challenge in challenges:
            raise ValueError("Each group needs its own independent challenge module")
        identifiers.add(label)
        configs.add(path)
        challenges.add(challenge)
        solutions.add(solution)
        suffix = "" if label == "main" else "-" + label
        groups.append({
            "id": label, "path": path.relative_to(root).as_posix(), "config": config,
            "exportDirectory": ".lake/final-exports" + suffix,
            "localReport": "submission/local-comparator" + suffix + "-result.json",
            "sandboxReport": "submission/comparator" + suffix + "-result.json",
        })
    if "main" not in identifiers:
        raise ValueError("The primary main comparison group is required")
    if challenges & solutions:
        raise ValueError("A proof module cannot be an independent challenge")
    main = next(group for group in groups if group["id"] == "main")
    if main["path"] != "comparator.json":
        raise ValueError("The main comparison config must remain comparator.json")
    return groups


def select_group(root, config_path="comparator.json"):
    root = Path(root).resolve()
    selected = (root / config_path).resolve()
    for group in load_groups(root):
        if (root / group["path"]).resolve() == selected:
            return group
    raise ValueError("The requested config is not a registered comparison group")


def declaration_names(groups):
    return list(dict.fromkeys(name for group in groups
        for name in group["config"]["theorem_names"] + group["config"].get("definition_names", [])))
