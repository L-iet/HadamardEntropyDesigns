/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyTranslationOrbits.TranslationOrbitCard
@[expose] public section
namespace EntropyDesigns.TranslationOrbits
open scoped BigOperators

 def translatedMatrix {J : Type*} (A : Matrix J J ℤ) (u : J → ℤ) : Matrix J J ℤ :=
  fun i j => A i j*u j

 theorem translated_matrix_is_hadamard {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (hn : 0<Fintype.card J)
    (u : J → ℤ) (hu : ∀ j,u j=1 ∨ u j= -1) : (translatedMatrix A u).IsHadamard := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
    obtain ha | ha := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i j)
    obtain hu | hu := hu j <;> simp [translatedMatrix,ha,hu]
    obtain hu | hu := hu j <;> simp [translatedMatrix,ha,hu]
  · have hentry (i k j : J) : (A i j*u j)*(A k j*u j)=A i j*A k j := by
      obtain h | h := hu j <;> simp [h]
    ext i k
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,
      translatedMatrix,hentry] using congr($hA.mul_conjTranspose i k)
  · apply isRegular_iff_ne_zero.mpr
    exact_mod_cast hn.ne'

 theorem translated_matrix_normalized {J : Type*} [DecidableEq J]
    (A : Matrix J J ℤ) (c₀ : J) (ha : ∀ i,A i c₀=1)
    (u : {j : J // j≠c₀} → Bool) : ∀ i,
    translatedMatrix A (translationMultiplier c₀ u) i c₀=1 := by
  intro i
  simp [translatedMatrix,translationMultiplier,ha]

 theorem normalized_hadamard_first_moment {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (c₀ : J)
    (ha : ∀ i,A i c₀=1) (c : J) (hc : c≠c₀) : ∑ i,A i c=0 := by
  have hh := congr($hA.conjTranspose_mul c c₀)
  simpa [Matrix.mul_apply,ha,hc] using hh

 theorem normalized_hadamard_same_moments {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (hn : 0<Fintype.card J)
    (c₀ : J) (ha : ∀ i,A i c₀=1) (u : {j : J // j≠c₀} → Bool) :
    (∀ c,c≠c₀ → (∑ i,translatedMatrix A (translationMultiplier c₀ u) i c)=∑ i,A i c) ∧
    (∀ c d,(∑ i,translatedMatrix A (translationMultiplier c₀ u) i c*
      translatedMatrix A (translationMultiplier c₀ u) i d)=∑ i,A i c*A i d) := by
  let B := translatedMatrix A (translationMultiplier c₀ u)
  have hb := translated_matrix_is_hadamard A hA hn _ (translation_multiplier_sign c₀ u)
  have hbn := translated_matrix_normalized A c₀ ha u
  constructor
  · intro c hc
    rw [normalized_hadamard_first_moment _ hb c₀ hbn c hc,
      normalized_hadamard_first_moment _ hA c₀ ha c hc]
  · intro c d
    have hga := congr($hA.conjTranspose_mul c d)
    have hgb := congr($hb.conjTranspose_mul c d)
    have he := hgb.trans hga.symm
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial] using he

 theorem hadamard_pair_pattern_count {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (c₀ : J) (ha : ∀ i,A i c₀=1)
    (c d : J) (hc : c≠c₀) (hd : d≠c₀) (hcd : c≠d)
    (σ τ : ℤ) (hσ : σ=1 ∨ σ= -1) (hτ : τ=1 ∨ τ= -1) :
    4*(Finset.univ.filter (fun i => A i c=σ ∧ A i d=τ)).card=(Fintype.card J:ℤ) := by
  classical
  have hind (i : J) : (if A i c=σ ∧ A i d=τ then (4:ℤ) else 0)=
      (1+σ*A i c)*(1+τ*A i d) := by
    obtain h1 | h1 := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i c)
    all_goals obtain h2 | h2 := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i d)
    all_goals obtain hσ | hσ := hσ
    all_goals obtain hτ | hτ := hτ
    all_goals simp [h1,h2,hσ,hτ]
  have hexp (i : J) : (1+σ*A i c)*(1+τ*A i d)=
      1+σ*A i c+τ*A i d+(σ*τ)*(A i c*A i d) := by ring
  have horth : (∑ i,A i c*A i d)=0 := by
    simpa [Matrix.mul_apply,hcd] using congr($hA.conjTranspose_mul c d)
  have hs : (∑ i,if A i c=σ ∧ A i d=τ then (4:ℤ) else 0)=(Fintype.card J:ℤ) := by
    simp_rw [hind,hexp]
    simp [Finset.sum_add_distrib,←Finset.mul_sum,
      normalized_hadamard_first_moment A hA c₀ ha c hc,
      normalized_hadamard_first_moment A hA c₀ ha d hd,horth]
  rw [←hs]
  simp [Finset.sum_ite,mul_comm]

 theorem bit_translation_preserves_pair_pattern_counts {J : Type*}
    [Fintype J] [DecidableEq J] (A : Matrix J J ℤ) (hA : A.IsHadamard)
    (hn : 0<Fintype.card J) (c₀ : J) (ha : ∀ i,A i c₀=1)
    (u : {j : J // j≠c₀} → Bool) (c d : J)
    (hc : c≠c₀) (hd : d≠c₀) (hcd : c≠d) (σ τ : ℤ)
    (hσ : σ=1 ∨ σ= -1) (hτ : τ=1 ∨ τ= -1) :
    (Finset.univ.filter (fun i => translatedMatrix A (translationMultiplier c₀ u) i c=σ ∧
      translatedMatrix A (translationMultiplier c₀ u) i d=τ)).card=
    (Finset.univ.filter (fun i => A i c=σ ∧ A i d=τ)).card := by
  have hb := translated_matrix_is_hadamard A hA hn _ (translation_multiplier_sign c₀ u)
  have hbn := translated_matrix_normalized A c₀ ha u
  have h1 := hadamard_pair_pattern_count A hA c₀ ha c d hc hd hcd σ τ hσ hτ
  have h2 := hadamard_pair_pattern_count _ hb c₀ hbn c d hc hd hcd σ τ hσ hτ
  omega

end EntropyDesigns.TranslationOrbits
