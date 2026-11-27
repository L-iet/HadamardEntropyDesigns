/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySymmetricCollision.MatchingLaws
public import EntropySymmetricCollision.CollisionResults
@[expose] public section
namespace EntropyDesigns.SymmetricEntropy
noncomputable section

theorem oddSymmetricLaw_collision_lower (m : ℕ) (hm : 1≤m) :
    1/((2*(m:ℝ)+1)+1)^2≤collision (oddSymmetricLaw m) := by
  rw [oddSymmetricLaw_collision]
  have hC : (0:ℝ)≤Nat.choose (2*m+1) m := Nat.cast_nonneg _
  have hh := div_nonneg (sq_nonneg ((2*(m:ℝ)+1)/(2*(m:ℝ)+2))) hC
  have he : (1/(2*(m:ℝ)+2))^2=1/((2*(m:ℝ)+1)+1)^2 := by field_simp; ring
  rw [he]
  linarith

theorem evenSymmetricLaw_collision_lower (m : ℕ) (hm : 1≤m) :
    1/(2*(2*(m:ℝ))^2)≤collision (evenSymmetricLaw m) := by
  rw [evenSymmetricLaw_collision m hm]
  have hC : (0:ℝ)≤Nat.choose (2*m) m := Nat.cast_nonneg _
  have hh := div_nonneg (sq_nonneg (1-1/(2*(m:ℝ)))) hC
  have he : 2*(1/(4*(m:ℝ)))^2=1/(2*(2*(m:ℝ))^2) := by field_simp; ring
  rw [he]
  linarith

theorem exists_matching_symmetric_law (d : ℕ) (hd : 2≤d) :
    ∃ w : (Fin d → Bool) → ℝ,IsSymmetricPairwiseLaw w ∧ 1/(4*(d:ℝ)^2)≤collision w := by
  obtain ⟨m,he|ho⟩ : ∃ m,d=2*m ∨ d=2*m+1 := ⟨d/2,by omega⟩
  · subst d
    have hm : 1≤m := by omega
    refine ⟨evenSymmetricLaw m,evenSymmetricLaw_valid m hm,?_⟩
    have hh := evenSymmetricLaw_collision_lower m hm
    have hc : 1/(4*(((2*m:ℕ):ℝ))^2)≤1/(2*(2*(m:ℝ))^2) := by
      push_cast
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [sq_nonneg (2*(m:ℝ))]
    exact hc.trans hh
  · subst d
    have hm : 1≤m := by omega
    refine ⟨oddSymmetricLaw m,oddSymmetricLaw_valid m hm,?_⟩
    have hh := oddSymmetricLaw_collision_lower m hm
    have hmR : (1:ℝ)≤m := by exact_mod_cast hm
    have hc : 1/(4*(((2*m+1:ℕ):ℝ))^2)≤1/((2*(m:ℝ)+1)+1)^2 := by
      push_cast
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [sq_nonneg (m:ℝ)]
    exact hc.trans hh

theorem small_symmetric_attainment (d : ℕ) (hd : 2≤d) (hd4 : d≤4) :
    ∃ w : (Fin d → Bool) → ℝ,IsSymmetricPairwiseLaw w ∧
      collision w=1/(roundedDimension (d+1):ℝ) := by
  rcases (show d=2 ∨ d=3 ∨ d=4 by omega) with rfl|rfl|rfl
  · refine ⟨evenSymmetricLaw 1,evenSymmetricLaw_valid 1 (by omega),?_⟩
    rw [evenSymmetricLaw_collision 1 (by omega)]
    norm_num [Nat.choose,roundedDimension]
  · refine ⟨oddSymmetricLaw 1,oddSymmetricLaw_valid 1 (by omega),?_⟩
    rw [oddSymmetricLaw_collision]
    norm_num [Nat.choose,roundedDimension]
  · refine ⟨evenSymmetricLaw 2,evenSymmetricLaw_valid 2 (by omega),?_⟩
    rw [evenSymmetricLaw_collision 2 (by omega)]
    norm_num [Nat.choose,roundedDimension]

end
end EntropyDesigns.SymmetricEntropy
