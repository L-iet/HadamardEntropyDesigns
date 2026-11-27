/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyTranslationOrbits.TranslationStabilizer
public import Mathlib.Data.Fintype.Pi
@[expose] public section
namespace EntropyDesigns.TranslationOrbits

noncomputable def translatedRows {J : Type*} [Fintype J]
    (A : Matrix J J ℤ) (u : J → ℤ) : Finset (J → ℤ) := by
  classical
  exact Finset.univ.image (fun i j => A i j*u j)

 theorem translated_rows_injective {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (hn : 4<Fintype.card J)
    (hmod : Fintype.card J%8=4) (u v : J → ℤ)
    (hu : ∀ j,u j=1 ∨ u j= -1) (hv : ∀ j,v j=1 ∨ v j= -1)
    (he : translatedRows A u=translatedRows A v) : u=v := by
  classical
  have hw (j : J) : u j*v j=1 ∨ u j*v j= -1 := by
    obtain hu | hu := hu j <;> obtain hv | hv := hv j <;> simp [hu,hv]
  have hstable (i : J) : ∃ k,∀ j,A k j=A i j*(u j*v j) := by
    have hm : (fun j => A i j*u j)∈translatedRows A v := by
      rw [←he]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hm
    refine ⟨k,fun j => ?_⟩
    have ht := congrFun hk j
    obtain hv | hv := hv j
    · simpa [hv] using ht
    · simp only [hv,mul_neg_one] at ht ⊢
      linear_combination -ht
  have htrivial := hadamard_sign_translation_stabilizer_trivial A hA hn hmod
    (fun j => u j*v j) hw hstable
  funext j
  have hh := htrivial j
  obtain hv | hv := hv j
  · simpa [hv] using hh
  · simp only [hv,mul_neg_one] at hh ⊢
    omega

 def translationMultiplier {J : Type*} [DecidableEq J] (c₀ : J)
    (u : {j : J // j≠c₀} → Bool) (j : J) : ℤ :=
  if h : j=c₀ then 1 else if u ⟨j,h⟩ then -1 else 1

 theorem translation_multiplier_sign {J : Type*} [DecidableEq J] (c₀ : J)
    (u : {j : J // j≠c₀} → Bool) (j : J) :
    translationMultiplier c₀ u j=1 ∨ translationMultiplier c₀ u j= -1 := by
  unfold translationMultiplier
  split_ifs <;> simp

 theorem translation_multiplier_injective {J : Type*} [DecidableEq J] (c₀ : J) :
    Function.Injective (translationMultiplier c₀) := by
  intro u v he
  funext j
  have hh := congrFun he j.val
  simp only [translationMultiplier,dif_neg j.property] at hh
  cases hu : u j <;> cases hv : v j <;> simp_all

 theorem bit_translation_row_sets_injective {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (hn : 4<Fintype.card J)
    (hmod : Fintype.card J%8=4) (c₀ : J) :
    Function.Injective (fun u : {j : J // j≠c₀} → Bool =>
      translatedRows A (translationMultiplier c₀ u)) := by
  intro u v he
  apply translation_multiplier_injective c₀
  exact translated_rows_injective A hA hn hmod _ _
    (translation_multiplier_sign c₀ u) (translation_multiplier_sign c₀ v) he

 theorem bit_translation_orbit_card {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (hn : 4<Fintype.card J)
    (hmod : Fintype.card J%8=4) (c₀ : J) :
    (Finset.univ.image (fun u : {j : J // j≠c₀} → Bool =>
      translatedRows A (translationMultiplier c₀ u))).card=2^(Fintype.card J-1) := by
  classical
  rw [Finset.card_image_of_injective _ (bit_translation_row_sets_injective A hA hn hmod c₀)]
  simp [Fintype.card_pi,Fintype.card_subtype_compl]

end EntropyDesigns.TranslationOrbits
