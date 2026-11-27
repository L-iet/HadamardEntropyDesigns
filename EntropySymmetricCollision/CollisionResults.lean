/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySymmetricCollision.CollisionRate
public import EntropySymmetricCollision.SmallCases
@[expose] public section
namespace EntropyDesigns.SymmetricEntropy
noncomputable section

theorem symmetric_no_attainment {d : ℕ} (hd : 5≤d)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hsym : CoordinatePermutationInvariant w)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    collision w≠1/(roundedDimension (d+1):ℝ) := by
  by_cases h5 : d=5
  · subst d
    simpa [roundedDimension] using five_bit_symmetric_no_attainment w hw hmass hsym hmean hpair
  · by_cases h6 : d=6
    · subst d
      simpa [roundedDimension] using six_bit_symmetric_no_attainment w hw hmass hsym hmean hpair
    · exact ne_of_lt (symmetric_no_attainment_large (by omega) w hw hmass hsym hmean hpair)

end
end EntropyDesigns.SymmetricEntropy
