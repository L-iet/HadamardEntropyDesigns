/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantitative.MomentError
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

theorem four_omitted_moment_error_floor {r : ℕ} (hr : 5≤r)
    (S : Finset (Finset (Fin r))) (horder : S.card=2^r-4)
    (rows : S → Fin (S.card-4) → Bool) (hmean : ∀ i,(∑ z,bitSign (rows z i))=0)
    (f : Fin (S.card-4) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r (r-2))
    (hm : ∀ (i : Fin (S.card-4)) (z : S),f i z.val=if rows z i then 1 else 0) :
    2*r-9≤(correlatedPairs rows).card ∧
      32*((2*r-9 : ℕ) : ℝ)/(S.card : ℝ)^2≤augmentedMomentError rows := by
  have hpow : 32≤2^r := Nat.pow_le_pow_right (by omega : 1≤2) hr
  have hdiv : 8∣2^r := by
    have he : r=3+(r-3) := by omega
    rw [he,pow_add]
    exact dvd_mul_right 8 _
  have hmod := Nat.mod_eq_zero_of_dvd hdiv
  have hres : S.card%8=4 := by omega
  have hp : S≠Finset.univ := by
    intro he
    have hcard := congrArg Finset.card he
    simp only [Finset.card_univ,Fintype.card_finset,Fintype.card_fin] at hcard
    omega
  have hT : (Sᶜ).card=4 := by
    simp only [Finset.card_compl,Fintype.card_finset,Fintype.card_fin]
    omega
  have hd := finrank_vectorSpan_image_finset_le (ZMod 2) (@booleanSupportVector r) Sᶜ (n:=3) hT
  have hdim : Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))≤3 := by
    have he : ((Sᶜ).image (@booleanSupportVector r) : Set (Fin r → ZMod 2))=omittedBooleanVectors S := by
      ext v
      constructor
      · intro hv
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
        exact ⟨z,by simpa using hz,rfl⟩
      · rintro ⟨z,hz,rfl⟩
        exact Finset.mem_image.mpr ⟨z,by simpa using hz,rfl⟩
    rw [he] at hd
    exact hd
  have hgen := punctured_moment_error_floor (by omega : 4≤r) S hres hp rows hmean f hf hm
  dsimp only at hgen
  have hA : 2*r-9≤2*(r-Module.finrank (ZMod 2)
      (vectorSpan (ZMod 2) (omittedBooleanVectors S)))-3 := by omega
  refine ⟨hA.trans hgen.1,?_⟩
  have hR : ((2*r-9 : ℕ) : ℝ)≤((2*(r-Module.finrank (ZMod 2)
      (vectorSpan (ZMod 2) (omittedBooleanVectors S)))-3 : ℕ) : ℝ) := by exact_mod_cast hA
  exact le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hR (by norm_num)) (sq_nonneg _)) hgen.2

end
end EntropyDesigns
