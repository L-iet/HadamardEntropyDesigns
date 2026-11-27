# SPDX-License-Identifier: Apache-2.0
"""Validate this project's licensed original construction-source inventory.

The function name matches the shared submission-scanner interface. This
project records its own EntropyDesigns sources rather than a sibling library.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def canonical_digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def construction_sources(root):
    directories = ("EntropyDesigns", "EntropySparseBuffer", "EntropyRadix", "HadamardMultibase", "EntropyTrades", "EntropyBoolean", "EntropyCubic", "EntropyAffine", "EntropySupport", "EntropyWitness", "EntropyQuantitative", "EntropySeedRepair", "EntropySymmetric", "EntropySymmetricCollision", "EntropyQuantum", "EntropyQuantumBounds", "EntropySupportFace", "EntropySupportDistance", "EntropyConcentration", "EntropyConcentratedFamily", "EntropyModerateSupport", "EntropyPlotkinSupport", "EntropySpanningSlopes", "EntropyRelativeSequence", "EntropyCompleteSequence", "EntropyExchangeableHierarchy", "EntropyGapTransfer", "EntropyPrimeTransfer", "EntropyProjectArithmetic", "EntropyProjectInstability", "EntropyDenominatorTrades", "EntropyPrimeExponentRigidity", "EntropyTranslationOrbits", "EntropyPermutationCost", "EntropyWeightedSimplex", "EntropyQuadraticClassification")
    roots = ("EntropyDesigns.lean", "Solution.lean", "CofiniteSolution.lean",
             "EntropySparseBuffer.lean", "BufferSolution.lean", "EntropyRadix.lean", "RadixSolution.lean", "EntropyTrades.lean", "TradeSolution.lean", "EntropyBoolean.lean", "BooleanSolution.lean", "EntropyCubic.lean", "CubicSolution.lean", "EntropyAffine.lean", "AffineSolution.lean", "EntropySupport.lean", "SupportSolution.lean", "EntropyWitness.lean", "WitnessSolution.lean", "EntropyQuantitative.lean", "MomentSolution.lean", "EntropySeedRepair.lean", "SeedRepairSolution.lean", "EntropySymmetric.lean", "SymmetricSolution.lean", "EntropySymmetricCollision.lean", "CollisionSolution.lean", "EntropyQuantum.lean", "QuantumSolution.lean", "EntropyQuantumBounds.lean", "QuantumBoundsSolution.lean", "EntropySupportFace.lean", "FaceSolution.lean", "EntropySupportDistance.lean", "DistanceSolution.lean", "EntropyConcentration.lean", "BarrierSolution.lean", "EntropyConcentratedFamily.lean", "FamilySolution.lean", "EntropyModerateSupport.lean", "ModerateSolution.lean", "EntropyPlotkinSupport.lean", "PlotkinSolution.lean", "EntropySpanningSlopes.lean", "SpanningSolution.lean", "EntropyRelativeSequence.lean", "RelativeSolution.lean", "EntropyCompleteSequence.lean", "SequenceSolution.lean", "EntropyExchangeableHierarchy.lean", "HierarchySolution.lean", "EntropyGapTransfer.lean", "GapSolution.lean", "EntropyPrimeTransfer.lean", "PrimeSolution.lean", "EntropyProjectArithmetic.lean", "EntropyProjectInstability.lean", "ProjectSolution.lean", "EntropyDenominatorTrades.lean", "DenominatorSolution.lean", "EntropyPrimeExponentRigidity.lean", "PrimeExponentSolution.lean", "EntropyTranslationOrbits.lean", "TranslationOrbitSolution.lean", "EntropyPermutationCost.lean", "PermutationCostSolution.lean", "EntropyWeightedSimplex.lean", "SimplexEntropySolution.lean", "EntropyQuadraticClassification.lean", "QuadraticClassificationSolution.lean")
    return {p.relative_to(root).as_posix() for name in directories
            for p in (root / name).rglob("*.lean")} | {
        name for name in roots if (root / name).is_file()}


def check_baseline_provenance():
    errors = []
    try:
        record = json.loads((ROOT / "submission/construction-source-provenance.json").read_text(encoding="utf-8"))
        if record.get("license") != "Apache-2.0" or record.get("licenseFile") != "LICENSE":
            errors.append("Construction source license metadata differs from Apache-2.0")
        if canonical_digest(ROOT / "LICENSE") != record.get("licenseCanonicalLFSHA256"):
            errors.append("Construction source license text changed")
        attributions = record.get("attributionFiles", [])
        expected_attributions = {"licenses/hadamard-finite-LICENSE.txt", "licenses/hadamard-finite-NOTICE.txt"}
        if (ROOT / "HadamardMultibase").is_dir() and not expected_attributions.issubset({x.get("file") for x in attributions}):
            errors.append("Missing licensed construction attribution records")
        for item in attributions:
            relative = Path(item["file"])
            if relative.is_absolute() or ".." in relative.parts or relative.parts[0] != "licenses":
                errors.append("Invalid construction attribution path")
                continue
            attribution = ROOT / relative
            if not attribution.is_file() or attribution.is_symlink() or canonical_digest(attribution) != item["canonicalLFSHA256"]:
                errors.append("Construction attribution file changed or missing: " + item["file"])
        current = construction_sources(ROOT)
        recorded = set()
        for item in record["sourceFiles"]:
            name = item["file"]
            if name not in current or name in recorded:
                errors.append("Invalid or duplicate construction source record: " + name)
                continue
            recorded.add(name)
            path = ROOT / name
            if not path.is_file() or path.is_symlink():
                errors.append("Missing or linked construction source: " + name)
            elif canonical_digest(path) != item["canonicalLFSHA256"]:
                errors.append("Construction source differs from licensed provenance: " + name)
        if recorded != current:
            errors.append("Construction source inventory differs from provenance manifest")
    except (OSError, ValueError, KeyError, TypeError) as exc:
        errors.append("Invalid construction source provenance: " + str(exc))
    return errors


if __name__ == "__main__":
    problems = check_baseline_provenance()
    print(json.dumps({"errors": problems, "licensedSourceSnapshotCurrent": not problems}, indent=2))
    raise SystemExit(bool(problems))
