/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySymmetricCollision.CollisionBound
@[expose] public section
namespace EntropyDesigns.SymmetricEntropy
noncomputable section

theorem collision_envelope_strict {x : ℝ} (hx : 7≤x) :
    1/x^2+x/(x-2)^4+2/(x*(x-1))<4/x^2 := by
  have hx0 : 0<x := by linarith
  have hx1 : 0<x-1 := by linarith
  have hx2 : 0<x-2 := by linarith
  have hy : 0≤x-7 := by linarith
  have hp : 0<2*(x-2)^4-3*x^3 := by
    have he : 2*(x-2)^4-3*x^3=
        2*(x-7)^4+37*(x-7)^3+237*(x-7)^2+559*(x-7)+221 := by ring
    rw [he]
    positivity
  have ha : x^3/(x-2)^4<2/3 := (div_lt_iff₀ (pow_pos hx2 4)).mpr (by nlinarith)
  have hb : 2*x/(x-1)≤7/3 := (div_le_iff₀ hx1).mpr (by linarith)
  have he : x^2*(1/x^2+x/(x-2)^4+2/(x*(x-1)))=
      1+x^3/(x-2)^4+2*x/(x-1) := by
    field_simp
    <;> ring
  have hc : x^2*(1/x^2+x/(x-2)^4+2/(x*(x-1)))<4 := by rw [he]; linarith
  apply (lt_div_iff₀ (sq_pos_of_pos hx0)).mpr
  nlinarith

theorem symmetric_collision_rate {d : ℕ} (hd : 7≤d)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hsym : CoordinatePermutationInvariant w)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    collision w<4/(d:ℝ)^2 :=
  (symmetric_collision_upper hd w hw hmass hsym hmean hpair).trans_lt
    (collision_envelope_strict (by exact_mod_cast hd))


theorem symmetric_no_attainment_large {d : ℕ} (hd : 7≤d)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hsym : CoordinatePermutationInvariant w)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    collision w<1/(roundedDimension (d+1):ℝ) := by
  have hN : 0<roundedDimension (d+1) ∧ roundedDimension (d+1)≤d+4 := by
    unfold roundedDimension
    omega
  have hNR : (0:ℝ)<roundedDimension (d+1) := by exact_mod_cast hN.1
  have hNd : (roundedDimension (d+1):ℝ)≤(d:ℝ)+4 := by exact_mod_cast hN.2
  have hdR : (7:ℝ)≤d := by exact_mod_cast hd
  have hd0 : (0:ℝ)<d := by linarith
  have hh : (4:ℝ)/(d:ℝ)^2<1/(roundedDimension (d+1):ℝ) := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos hd0) hNR).mpr
    nlinarith [sq_nonneg ((d:ℝ)-7)]
  exact (symmetric_collision_rate hd w hw hmass hsym hmean hpair).trans hh

end
end EntropyDesigns.SymmetricEntropy
