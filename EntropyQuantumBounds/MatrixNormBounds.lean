/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantumBounds.EuclideanEffects
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem effect_matrix_defect_norm (a N : ℝ) (hN : 0<N)
    (ha : 0≤a*N) (ha1 : a*N≤1) (v : ι → ℝ) (hnorm : inner v v=N) :
    euclideanOperatorNorm (effect a v-effect a v*effect a v)=(a*N)*(1-a*N) := by
  unfold euclideanOperatorNorm
  simp only [map_sub,map_mul,effect_normalized_rankOne a N hN v]
  exact unit_effect_defect_norm (a*N) ha ha1 (normalizedRow N v) (normalizedRow_norm N hN v hnorm)

theorem effect_matrix_commutator_bound (a N : ℝ) (hN : 0<N)
    (v w : ι → ℝ) (hv : inner v v=N) (hw : inner w w=N) :
    euclideanOperatorNorm (commutator (effect a v) (effect a w))≤(a*N)^2*|inner v w/N| := by
  unfold euclideanOperatorNorm commutator
  simp only [map_sub,map_mul,effect_normalized_rankOne a N hN v,effect_normalized_rankOne a N hN w]
  have h := unit_effect_commutator_bound (a*N) (normalizedRow N v) (normalizedRow N w)
    (normalizedRow_norm N hN v hv) (normalizedRow_norm N hN w hw)
  simpa only [normalizedRow_inner N hN v w] using h
end
end EntropyDesigns.Quantum
