/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantitative.CorrelatedPairs
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

def augmentedObservable {ι : Type*} {m : ℕ} (rows : ι → Fin m → Bool)
    (z : ι) : Fin (m+1) → ℤ := Fin.cons 1 (fun i => bitSign (rows z i))

def momentEntryError {ι : Type*} [Fintype ι] {m : ℕ} (rows : ι → Fin m → Bool)
    (i j : Fin (m+1)) : ℝ :=
  (((∑ z,((augmentedObservable rows z i : ℝ)*(augmentedObservable rows z j : ℝ)))/
    (Fintype.card ι : ℝ))-(if i=j then 1 else 0))^2

def augmentedMomentError {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) : ℝ :=
  ∑ ij : Fin (m+1) × Fin (m+1),momentEntryError rows ij.1 ij.2

def orientedCorrelatedPairs {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) : Finset (Fin m × Fin m) :=
  correlatedPairs rows ∪ (correlatedPairs rows).image Prod.swap

theorem oriented_correlated_pairs_card {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) : (orientedCorrelatedPairs rows).card=2*(correlatedPairs rows).card := by
  classical
  have hd : Disjoint (correlatedPairs rows) ((correlatedPairs rows).image Prod.swap) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨b,hbin,rfl⟩ := Finset.mem_image.mp hb
    have h1 := (Finset.mem_filter.mp ha).2.1
    have h2 := (Finset.mem_filter.mp hbin).2.1
    change b.2 < b.1 at h1
    omega
  have hi : Function.Injective (@Prod.swap (Fin m) (Fin m)) := by
    intro a b h
    have he := congrArg Prod.swap h
    simpa using he
  rw [orientedCorrelatedPairs,Finset.card_union_of_disjoint hd,Finset.card_image_of_injective _ hi]
  omega

theorem oriented_correlated_pair_properties {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) (p : Fin m × Fin m) (hp : p∈orientedCorrelatedPairs rows) :
    p.1≠p.2 ∧ signCorrelation rows p.1 p.2≠0 := by
  classical
  rcases Finset.mem_union.mp hp with hp|hp
  · have h := (Finset.mem_filter.mp hp).2
    exact ⟨ne_of_lt h.1,h.2⟩
  · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have h := (Finset.mem_filter.mp hq).2
    refine ⟨ne_of_gt h.1,?_⟩
    change signCorrelation rows q.2 q.1≠0
    simpa only [signCorrelation_symm rows q.2 q.1] using h.2

theorem off_diagonal_moment_error {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) (i j : Fin m) (hne : i≠j) :
    momentEntryError rows i.succ j.succ=
      (signCorrelation rows i j : ℝ)^2/(Fintype.card ι : ℝ)^2 := by
  have hs : i.succ≠j.succ := fun h => hne (Fin.succ_injective m h)
  have hc : (∑ z,((bitSign (rows z i) : ℝ)*(bitSign (rows z j) : ℝ)))=
      (signCorrelation rows i j : ℝ) := by simp [signCorrelation]
  unfold momentEntryError
  simp only [augmentedObservable,Fin.cons_succ,if_neg hs,sub_zero]
  rw [hc,div_pow]

theorem balanced_moment_error_pair_bound {ι : Type*} [Fintype ι] {m : ℕ}
    (hN : Fintype.card ι%4=0) (rows : ι → Fin m → Bool)
    (hmean : ∀ i,(∑ z,bitSign (rows z i))=0) :
    32*(correlatedPairs rows).card/(Fintype.card ι : ℝ)^2≤augmentedMomentError rows := by
  classical
  let e : (Fin m × Fin m) → (Fin (m+1) × Fin (m+1)) := fun p => (p.1.succ,p.2.succ)
  have he : Function.Injective e := by
    intro a b h
    apply Prod.ext
    · exact Fin.succ_injective m (congrArg Prod.fst h)
    · exact Fin.succ_injective m (congrArg Prod.snd h)
  let I := (orientedCorrelatedPairs rows).image e
  have hcard : I.card=2*(correlatedPairs rows).card := by
    rw [Finset.card_image_of_injective _ he,oriented_correlated_pairs_card]
  have hpoint : ∀ ij∈I,(16 : ℝ)/(Fintype.card ι : ℝ)^2≤momentEntryError rows ij.1 ij.2 := by
    intro ij hij
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hij
    obtain ⟨hne,hcorr⟩ := oriented_correlated_pair_properties rows p hp
    have hq := balanced_nonzero_correlation_square hN rows p.1 p.2 (hmean p.1) (hmean p.2) hcorr
    have hqR : (16 : ℝ)≤(signCorrelation rows p.1 p.2 : ℝ)^2 := by exact_mod_cast hq
    change _≤momentEntryError rows p.1.succ p.2.succ
    rw [off_diagonal_moment_error rows _ _ hne]
    exact div_le_div_of_nonneg_right hqR (sq_nonneg _)
  have hsum := Finset.sum_le_sum (s:=I) (fun p hp => hpoint p hp)
  have hsub : (∑ p∈I,momentEntryError rows p.1 p.2)≤augmentedMomentError rows := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro p _ _
    exact sq_nonneg _
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  rw [hcard] at hsum
  push_cast at hsum
  calc
    _ = (2*(correlatedPairs rows).card : ℝ)*(16/(Fintype.card ι : ℝ)^2) := by ring
    _ ≤ _ := hsum.trans hsub

theorem punctured_moment_error_floor {r : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hres : S.card%8=4) (hproper : S≠Finset.univ)
    (rows : S → Fin (S.card-4) → Bool) (hmean : ∀ i,(∑ z,bitSign (rows z i))=0)
    (f : Fin (S.card-4) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r (r-2))
    (hm : ∀ (i : Fin (S.card-4)) (z : S),f i z.val=if rows z i then 1 else 0) :
    let a := r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))
    2*a-3≤(correlatedPairs rows).card ∧
      32*((2*a-3 : ℕ) : ℝ)/(S.card : ℝ)^2≤augmentedMomentError rows := by
  dsimp only
  have hc := punctured_correlation_count_lower hr S hres hproper rows hmean f hf hm
  refine ⟨hc,?_⟩
  have hN4 : Fintype.card S%4=0 := by simp only [Fintype.card_coe]; omega
  have hb := balanced_moment_error_pair_bound hN4 rows hmean
  simp only [Fintype.card_coe] at hb
  have hR : ((2*(r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S)))-3 : ℕ) : ℝ)≤
      ((correlatedPairs rows).card : ℝ) := by exact_mod_cast hc
  exact le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hR (by norm_num)) (sq_nonneg _)) hb

end
end EntropyDesigns
