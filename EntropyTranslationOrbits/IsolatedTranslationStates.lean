/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyTranslationOrbits.TranslationFiber
public import EntropyPrimeExponentRigidity.InfiniteFibers
@[expose] public section
namespace EntropyDesigns.TranslationOrbits
open scoped BigOperators

 theorem translated_row_set_card {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (hn : 0<Fintype.card J)
    (u : J → ℤ) (hu : ∀ j,u j=1 ∨ u j= -1) :
    (translatedRows A u).card=Fintype.card J := by
  classical
  have hinj := hadamard_rows_injective _ (translated_matrix_is_hadamard A hA hn u hu) hn
  change (Finset.univ.image (translatedMatrix A u)).card=Fintype.card J
  exact (Finset.card_image_of_injective Finset.univ hinj).trans (Finset.card_univ)

 theorem hadamard_normalize_column {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (hn : 0<Fintype.card J) (c₀ : J) :
    ∃ B : Matrix J J ℤ,B.IsHadamard ∧ ∀ i,B i c₀=1 := by
  let B := (translatedMatrix A.transpose (fun i => A i c₀)).transpose
  have ht : A.transpose.IsHadamard := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.conjTranspose
  have hs : ∀ i,A i c₀=1 ∨ A i c₀= -1 := fun i =>
    Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i c₀)
  have hb := translated_matrix_is_hadamard A.transpose ht hn (fun i => A i c₀) hs
  refine ⟨B,?_,?_⟩
  · simpa only [B,Matrix.conjTranspose_eq_transpose_of_trivial] using hb.conjTranspose
  · intro i
    obtain h | h := hs i <;> simp [B,translatedMatrix,Matrix.transpose_apply,h]

 theorem all_translated_states_isolated (n R : ℕ)
    (hRigid : PrimeExponentRigidity.IsRigidOrderAtDegree n R)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsHadamard) (hn : 0<n)
    (c₀ : Fin n) (u : {j : Fin n // j≠c₀} → Bool)
    (B : Matrix (Fin n) (Fin n) ℤ) (S : Finset (Fin n))
    (ht : DenominatorTrades.IsReducedNormalizedObservationTrade
      (translatedMatrix A (translationMultiplier c₀ u)) B c₀ S)
    (hdegree : S.card≤R) : S=∅ := by
  exact hRigid _ B c₀ S
    (translated_matrix_is_hadamard A hA (by simpa using hn) _
      (translation_multiplier_sign c₀ u)) ht hdegree

 theorem exponential_multiplicity_of_states {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (hn : 4<Fintype.card J)
    (hmod : Fintype.card J%8=4) (c₀ : J) (ha : ∀ i,A i c₀=1) :
    (Finset.univ.image (fun u : {j : J // j≠c₀} → Bool =>
      translatedRows A (translationMultiplier c₀ u))).card=2^(Fintype.card J-1) ∧
    ∀ u : {j : J // j≠c₀} → Bool,
      (translatedRows A (translationMultiplier c₀ u)).card=Fintype.card J ∧
      (translatedMatrix A (translationMultiplier c₀ u)).IsHadamard ∧
      (∀ i,translatedMatrix A (translationMultiplier c₀ u) i c₀=1) ∧
      ∀ c d,c≠c₀ → d≠c₀ → c≠d → ∀ σ τ : ℤ,
        (σ=1 ∨ σ= -1) → (τ=1 ∨ τ= -1) →
        (Finset.univ.filter (fun i => translatedMatrix A (translationMultiplier c₀ u) i c=σ ∧
          translatedMatrix A (translationMultiplier c₀ u) i d=τ)).card=
        (Finset.univ.filter (fun i => A i c=σ ∧ A i d=τ)).card := by
  refine ⟨bit_translation_orbit_card A hA hn hmod c₀,fun u => ?_⟩
  have hpos : 0<Fintype.card J := by omega
  exact ⟨translated_row_set_card A hA hpos _ (translation_multiplier_sign c₀ u),
    translated_matrix_is_hadamard A hA hpos _ (translation_multiplier_sign c₀ u),
    translated_matrix_normalized A c₀ ha u,
    fun c d hc hd hcd σ τ hσ hτ =>
      bit_translation_preserves_pair_pattern_counts A hA hpos c₀ ha u c d hc hd hcd σ τ hσ hτ⟩

 theorem unbounded_orders_with_exponentially_many_isolated_states (R N : ℕ) :
    ∃ n : ℕ,N<n ∧ 4<n ∧ n%8=4 ∧
      ∃ A : Matrix (Fin n) (Fin n) ℤ,∃ c₀ : Fin n,
        A.IsHadamard ∧ (∀ i,A i c₀=1) ∧
        (Finset.univ.image (fun u : {j : Fin n // j≠c₀} → Bool =>
          translatedRows A (translationMultiplier c₀ u))).card=2^(n-1) ∧
        ∀ u : {j : Fin n // j≠c₀} → Bool,∀ B : Matrix (Fin n) (Fin n) ℤ,
          ∀ S : Finset (Fin n),DenominatorTrades.IsReducedNormalizedObservationTrade
            (translatedMatrix A (translationMultiplier c₀ u)) B c₀ S →
              S.card≤R → S=∅ := by
  obtain ⟨n,hn,hres,⟨A,hA⟩,hRigid⟩ :=
    PrimeExponentRigidity.unbounded_known_rigid_orders R (max N 4)
  have hnN : N<n := lt_of_le_of_lt (Nat.le_max_left _ _) hn
  have hn4 : 4<n := lt_of_le_of_lt (Nat.le_max_right _ _) hn
  let c₀ : Fin n := ⟨0,by omega⟩
  obtain ⟨B,hB,hbn⟩ := hadamard_normalize_column A hA (by simpa using (show 0<n by omega)) c₀
  refine ⟨n,hnN,hn4,hres,B,c₀,hB,hbn,?_,?_⟩
  · simpa only [Fintype.card_fin] using
      bit_translation_orbit_card B hB (by simpa using hn4) (by simpa using hres) c₀
  · intro u C S ht hs
    exact all_translated_states_isolated n R hRigid B hB (by omega) c₀ u C S ht hs

end EntropyDesigns.TranslationOrbits
