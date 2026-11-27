#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Local diagnostic for one selected group; not a registry report.
python3 scripts/run_local_comparator.py --config "${1:-comparator.json}"
