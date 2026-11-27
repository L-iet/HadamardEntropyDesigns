module

public import EntropyDesigns.WalshInversion
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Finset.SDiff

/-! # Additive coverage of binary masks and exact moment rigidity -/

@[expose] public section
namespace EntropyDesigns
open scoped symmDiff

theorem walshChar_product {d : ℕ} (S T : Finset (Fin d)) (x : Fin d → Bool) :
    walshChar (S ∆ T) x = walshChar S x * walshChar T x := by
  have hfull : ∀ S : Finset (Fin d), walshChar S x =
      ∏ i : Fin d, if i ∈ S then bitSign (x i) else 1 := by
    intro S
    simp [walshChar]
  rw [hfull, hfull, hfull, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hsq : bitSign (x i) * bitSign (x i) = 1 := by
    rcases bitSign_sign (x i) with h | h <;> simp [h]
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [Finset.mem_symmDiff, hS, hT, hsq]

theorem walshCoefficient_symmDiff {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (S T : Finset (Fin d)) :
    walshCoefficient w (S ∆ T) =
      ∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ) := by
  simp [walshCoefficient, walshChar_product, mul_assoc]

def maskSumset {d : ℕ} (A : Finset (Finset (Fin d))) : Finset (Finset (Fin d)) :=
  A.biUnion (fun S => A.image (fun T => S ∆ T))

theorem mem_maskSumset {d : ℕ} (A : Finset (Finset (Fin d))) (c : Finset (Fin d)) :
    c ∈ maskSumset A ↔ ∃ S ∈ A, ∃ T ∈ A, S ∆ T = c := by
  simp [maskSumset]

theorem observed_moments_iff_mask_cover {d : ℕ} (B : Finset (Finset (Fin d)))
    (hB : ∅ ∉ B) (w : (Fin d → Bool) → ℝ) :
    ((∀ S ∈ B, walshCoefficient w S = 0) ∧
      (∀ S ∈ B, ∀ T ∈ B, S ≠ T →
        ∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ) = 0)) ↔
    ∀ c ∈ maskSumset (insert ∅ B), c ≠ ∅ → walshCoefficient w c = 0 := by
  classical
  constructor
  · rintro ⟨hmean, hpair⟩ c hc hnonzero
    obtain ⟨S, hS, T, hT, hsum⟩ := (mem_maskSumset _ c).mp hc
    rcases Finset.mem_insert.mp hS with rfl | hS
    · have hTc : T = c := by simpa [Finset.symmDiff_def] using hsum
      have hTne : T ≠ ∅ := hTc.symm ▸ hnonzero
      rw [← hTc]
      exact hmean T ((Finset.mem_insert.mp hT).resolve_left hTne)
    · rcases Finset.mem_insert.mp hT with rfl | hT
      · have hSc : S = c := by simpa [Finset.symmDiff_def] using hsum
        rw [← hSc]
        exact hmean S hS
      · have hST : S ≠ T := by
          intro h
          subst T
          have : c = ∅ := by simpa using hsum.symm
          exact hnonzero this
        rw [← hsum, walshCoefficient_symmDiff]
        exact hpair S hS T hT hST
  · intro hzero
    constructor
    · intro S hS
      apply hzero S
      · exact (mem_maskSumset _ _).mpr
          ⟨S, Finset.mem_insert_of_mem hS, ∅, by simp, by simp⟩
      · intro h
        exact hB (h ▸ hS)
    · intro S hS T hT hST
      rw [← walshCoefficient_symmDiff]
      apply hzero (S ∆ T)
      · exact (mem_maskSumset _ _).mpr
          ⟨S, Finset.mem_insert_of_mem hS, T, Finset.mem_insert_of_mem hT, rfl⟩
      · simpa using hST

theorem full_mask_cover_uniform {d : ℕ} (B : Finset (Finset (Fin d)))
    (hB : ∅ ∉ B) (hcover : maskSumset (insert ∅ B) = Finset.univ)
    (w : (Fin d → Bool) → ℝ) (hmass : ∑ x, w x = 1)
    (hmoments : (∀ S ∈ B, walshCoefficient w S = 0) ∧
      (∀ S ∈ B, ∀ T ∈ B, S ≠ T →
        ∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ) = 0)) :
    ∀ x, w x = 1 / (2 : ℝ) ^ d := by
  apply walsh_uniform_of_nonconstant_zero w hmass
  intro S hS
  apply (observed_moments_iff_mask_cover B hB w).mp hmoments S
  · rw [hcover]
    exact Finset.mem_univ S
  · exact Finset.nonempty_iff_ne_empty.mp hS

def maskTranslate {d : ℕ} (c : Finset (Fin d)) : Finset (Fin d) ≃ Finset (Fin d) where
  toFun S := S ∆ c
  invFun S := S ∆ c
  left_inv S := by simp
  right_inv S := by simp

theorem more_than_half_mask_cover {d : ℕ} (A : Finset (Finset (Fin d)))
    (hlarge : 2 ^ d < 2 * A.card) : maskSumset A = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro c
  let T := A.image (maskTranslate c)
  have hcardT : T.card = A.card := Finset.card_image_of_injective _ (maskTranslate c).injective
  have hbound : (A ∪ T).card ≤ 2 ^ d := by
    simpa using Finset.card_le_univ (A ∪ T)
  have hcount := Finset.card_union_add_card_inter A T
  have hinter : 0 < (A ∩ T).card := by omega
  obtain ⟨S, hS⟩ := Finset.card_pos.mp hinter
  obtain ⟨hSA, hST⟩ := Finset.mem_inter.mp hS
  obtain ⟨R, hRA, hRS⟩ := Finset.mem_image.mp hST
  apply (mem_maskSumset A c).mpr
  refine ⟨R, hRA, S, hSA, ?_⟩
  rw [← hRS]
  change R ∆ (R ∆ c) = c
  simp

end EntropyDesigns
