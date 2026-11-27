/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupport.PuncturedObservables
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

theorem booleanCode_dimension_binomial_sum (r D : ℕ) :
    Module.finrank (ZMod 2) (lowDegreeBooleanCode r D)=∑ j∈Finset.range (D+1),Nat.choose r j := by
  classical
  let A : Finset (Finset (Fin r)) := Finset.univ.filter (fun s => s.card≤D)
  have ha : Module.finrank (ZMod 2) (lowDegreeBooleanCode r D)=A.card := by
    rw [lowDegreeBooleanCode_finrank]
    simp [A,Fintype.card_subtype]
  rw [ha]
  have hc : (A : Set (Finset (Fin r))).MapsTo Finset.card (Finset.range (D+1)) := by
    intro s hs
    have hsA : s∈A := hs
    have hsc : s.card≤D := (Finset.mem_filter.mp hsA).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hsc)
  rw [Finset.card_eq_sum_card_fiberwise hc]
  apply Finset.sum_congr rfl
  intro j hj
  have hjD : j≤D := by have := Finset.mem_range.mp hj; omega
  have he : A.filter (fun s => s.card=j)=Finset.univ.filter (fun s : Finset (Fin r) => s.card=j) := by
    ext s
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  rw [he]
  have hh := Fintype.card_finset_len (α:=Fin r) j
  simpa [Fintype.card_subtype] using hh

theorem punctured_observable_minimal_degree {r D : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hN : 12≤S.card) (hres : S.card%8=4)
    (hlo : 2^(r-1)<S.card)
    (rows : S → Fin (S.card-4) → Bool) (hrows : IsUniformBinaryPairwiseIndependent rows)
    (f : Fin (S.card-4) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r D)
    (hm : ∀ (i : Fin (S.card-4)) (z : S),f i z.val=if rows z i then 1 else 0) :
    r≤2*D := by
  have hd := punctured_observable_code_dimension S hN hres rows hrows f hf hm
  by_contra! hD
  have hb := lowDegreeBooleanCode_half_dimension hD
  have he : 2^r=2*2^(r-1) := by
    conv_lhs => rw [show r=(r-1)+1 by omega,pow_succ]
    omega
  have hdiv : 8∣2^(r-1) := by
    have he : r-1=3+(r-4) := by omega
    rw [he,pow_add]
    exact dvd_mul_right 8 _
  have hz := Nat.mod_eq_zero_of_dvd hdiv
  rw [he] at hb
  generalize hv : 2^(r-1)=v at *
  omega

theorem four_omitted_punctured_encoding_impossible {r : ℕ} (hr : 5≤r)
    (S : Finset (Finset (Fin r))) (horder : S.card=2^r-4)
    (rows : S → Fin (S.card-4) → Bool) (hrows : IsUniformBinaryPairwiseIndependent rows)
    (f : Fin (S.card-4) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r (r-2))
    (hm : ∀ (i : Fin (S.card-4)) (z : S),f i z.val=if rows z i then 1 else 0) : False := by
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
  have hb := punctured_observable_affine_codimension (by omega) S (by omega) hres hp rows hrows f hf hm
  omega

theorem punctured_observable_bounds {r D : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hN : 12≤S.card) (hres : S.card%8=4)
    (hproper : S≠Finset.univ)
    (rows : S → Fin (S.card-4) → Bool) (hrows : IsUniformBinaryPairwiseIndependent rows)
    (f : Fin (S.card-4) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r D)
    (hm : ∀ (i : Fin (S.card-4)) (z : S),f i z.val=if rows z i then 1 else 0) :
    S.card-3≤∑ j∈Finset.range (D+1),Nat.choose r j ∧
    (2^(r-1)<S.card → r≤2*D) ∧
    (D≤r-2 → r-1≤Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))) := by
  refine ⟨?_,?_,?_⟩
  · rw [← booleanCode_dimension_binomial_sum]
    exact punctured_observable_code_dimension S hN hres rows hrows f hf hm
  · intro hlo
    exact punctured_observable_minimal_degree hr S hN hres hlo rows hrows f hf hm
  · intro hD
    exact punctured_observable_affine_codimension hr S hN hres hproper rows hrows f
      (fun i => lowDegreeBooleanCode_mono hD (hf i)) hm

end
end EntropyDesigns
