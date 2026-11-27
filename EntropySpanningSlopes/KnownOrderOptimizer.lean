/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySpanningSlopes.NormalizedLaw
public import EntropySpanningSlopes.HadamardNormalization
public import EntropySupportDistance.SourceRowBridge
public import EntropySupportDistance.OffsetHadamard
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SpanningSlopes
noncomputable section
open SupportFace

def sourceIndexEquiv {k s : ℕ} (i0 : Fin k) :
    (Fin k × (Fin s → Bool)) ≃ Option (SourceCoordinate k s i0) :=
  (Equiv.prodCongr (Equiv.refl (Fin k)) (maskSeedEquiv s).symm).trans (fullColumnEquiv i0)

theorem sourceIndexEquiv_none {k s : ℕ} (i0 : Fin k) :
    (sourceIndexEquiv (s:=s) i0).symm none=(i0,fun _ => false) := by
  simp [sourceIndexEquiv,fullColumnEquiv,maskSeedEquiv]
  funext j
  simp [maskSeed]

theorem source_optimizer_of_known_hadamard {k s : ℕ} (i0 : Fin k)
    (e : Finset (Fin s)) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    ∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
      (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) := by
  let NK := normalizeSignMatrix K i0
  let c : BlockSeeds k s := fun _ _ => false
  let ρ := sourceIndexEquiv (s:=s) i0
  let A := Matrix.reindex ρ ρ (offsetHadamard e i0 c NK)
  have hNK : Matrix.IsHadamard NK := normalizeSignMatrix_isHadamard K hK i0
  have hA : Matrix.IsHadamard A := (offsetHadamard_isHadamard e i0 c NK hNK).reindex ρ ρ
  have hcol : ∀ r,A r none=1 := by
    intro r
    change offsetHadamard e i0 c NK (ρ.symm r) (ρ.symm none)=1
    have hn : ρ.symm none=(i0,fun _ => false) := sourceIndexEquiv_none i0
    rw [hn]
    have hmask : seedMask (fun _ : Fin s => false)=∅ := by
      ext j
      simp [seedMask]
    change NK (ρ.symm r).1 i0 * fullSourceRow e i0 (offsetSeed c (ρ.symm r).2)
      (i0,seedMask (fun _ : Fin s => false))=1
    rw [hmask]
    have hNKcol : NK (ρ.symm r).1 i0=1 := normalizeSignMatrix_column K hK i0 _
    rw [hNKcol,one_mul]
    have hb := fullSourceRow_column_bridge e i0 (offsetSeed c (ρ.symm r).2) none
    exact hb
  exact normalized_hadamard_source_optimizer i0 A hA hcol

end
end EntropyDesigns.SpanningSlopes
