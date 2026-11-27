/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.SupportOverlap
public import Mathlib.Analysis.Convex.Hull
@[expose] public section
namespace EntropyDesigns.SupportWitness
open scoped BigOperators
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def IsClique (R : α → α → Prop) (T : Finset α) : Prop :=
  ∀ a∈T,∀ b∈T,a≠b → R a b

def orthogonalityNumber (R : α → α → Prop) (S : Finset α) : ℕ := by
  classical
  exact S.powerset.sup fun T => if IsClique R T then T.card else 0

def blockLaws (R : α → α → Prop) (n : ℕ) : Set (α → ℝ) :=
  {q | ∃ T : Finset α,T.card=n ∧ IsClique R T ∧ q=uniformFiniteLaw T}

theorem clique_card_le (R : α → α → Prop) (S T : Finset α)
    (hsub : T⊆S) (hT : IsClique R T) : T.card≤orthogonalityNumber R S := by
  classical
  unfold orthogonalityNumber
  have h := Finset.le_sup (f:=fun U : Finset α => if IsClique R U then U.card else 0)
    (Finset.mem_powerset.mpr hsub)
  simpa [hT] using h

theorem block_support_mass_le (R : α → α → Prop) (S : Finset α) {n : ℕ}
    (hn : 0<n) {q : α → ℝ} (hq : q∈blockLaws R n) :
    (∑ x∈S,q x)≤(orthogonalityNumber R S : ℝ)/n := by
  classical
  obtain ⟨T,hcard,hT,rfl⟩ := hq
  have hc := clique_card_le R S (S∩T) Finset.inter_subset_left
    (by
      intro a ha b hb hab
      exact hT a (Finset.mem_inter.mp ha).2 b (Finset.mem_inter.mp hb).2 hab)
  have he : (∑ x∈S,uniformFiniteLaw T x)=((S∩T).card : ℝ)/(n : ℝ) := by
    simp [uniformFiniteLaw,Finset.sum_ite,Finset.filter_mem_eq_inter,hcard,div_eq_mul_inv]
  rw [he]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

theorem mixtures_probability_and_cap (R : α → α → Prop) (S : Finset α) {n : ℕ}
    (hn : 0<n) {q : α → ℝ} (hq : q∈convexHull ℝ (blockLaws R n)) :
    (∀ x,0≤q x) ∧ (∑ x,q x)=1 ∧
      (∑ x∈S,q x)≤(orthogonalityNumber R S : ℝ)/n := by
  classical
  let C : Set (α → ℝ) := {q | (∀ x,0≤q x) ∧ (∑ x,q x)=1 ∧
    (∑ x∈S,q x)≤(orthogonalityNumber R S : ℝ)/n}
  have hbase : blockLaws R n⊆C := by
    intro q hq
    have hc := block_support_mass_le R S hn hq
    obtain ⟨T,hT,_,rfl⟩ := hq
    exact ⟨uniformFiniteLaw_nonneg T,uniformFiniteLaw_mass T (by omega),hc⟩
  have hconv : Convex ℝ C := by
    intro p hp q hq a b ha hb hab
    refine ⟨?_,?_,?_⟩
    · intro x
      exact add_nonneg (mul_nonneg ha (hp.1 x)) (mul_nonneg hb (hq.1 x))
    · change (∑ x,(a*p x+b*q x))=1
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hp.2.1,hq.2.1]
      simpa using hab
    · change (∑ x∈S,(a*p x+b*q x))≤_
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
      calc
        _ ≤ a*((orthogonalityNumber R S : ℝ)/n)+b*((orthogonalityNumber R S : ℝ)/n) :=
          add_le_add (mul_le_mul_of_nonneg_left hp.2.2 ha) (mul_le_mul_of_nonneg_left hq.2.2 hb)
        _ = _ := by rw [←add_mul,hab,one_mul]
  exact convexHull_min hbase hconv hq

theorem subset_mass_le_variation (p q : α → ℝ) (hm : (∑ x,p x)=(∑ x,q x)) (S : Finset α) :
    (∑ x∈S,p x)-(∑ x∈S,q x)≤totalVariation p q := by
  classical
  have hh (x : α) : (if x∈S then p x-q x else q x-p x)≤|p x-q x| := by
    by_cases hx : x∈S
    · simpa [hx] using le_abs_self (p x-q x)
    · simpa [hx] using neg_le_abs (p x-q x)
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => hh x)
  have hzero : (∑ x,(p x-q x))=0 := by rw [Finset.sum_sub_distrib,hm,sub_self]
  have hpart := Finset.sum_add_sum_compl S (fun x => p x-q x)
  have hleft : (∑ x,if x∈S then p x-q x else q x-p x)=
      (∑ x∈S,(p x-q x))-(∑ x∈Sᶜ,(p x-q x)) := by
    have hc : (Finset.univ.filter fun x : α => x∉S)=Sᶜ := by ext x; simp
    simp [Finset.sum_ite,Finset.sum_sub_distrib,hc]
    <;> ring
  rw [hleft] at h
  rw [hzero] at hpart
  unfold totalVariation
  rw [Finset.sum_sub_distrib] at h hpart
  linarith

theorem support_witness_all_mixtures (R : α → α → Prop) (S : Finset α) {n : ℕ}
    (hn : 0<n) (p : α → ℝ) (hp : ∑ x,p x=1)
    (hsupport : ∀ x,x∉S → p x=0) (q : α → ℝ)
    (hq : q∈convexHull ℝ (blockLaws R n)) :
    1-(orthogonalityNumber R S : ℝ)/n≤totalVariation p q := by
  classical
  obtain ⟨_,hqmass,hqcap⟩ := mixtures_probability_and_cap R S hn hq
  have hpmass : (∑ x∈S,p x)=1 := by
    rw [←hp]
    exact Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => hsupport x hx)
  have h := subset_mass_le_variation p q (hp.trans hqmass.symm) S
  rw [hpmass] at h
  linarith

theorem retained_per_block_le (R : α → α → Prop) (S : Finset α) {n : ℕ}
    (x y : Fin n → α) (hx : ∀ i,x i∈S) (hy : Function.Injective y)
    (horth : ∀ i j,i≠j → R (y i) (y j)) :
    (Finset.univ.filter fun i => x i=y i).card≤orthogonalityNumber R S := by
  classical
  let I := Finset.univ.filter fun i => x i=y i
  have hsub : I.image y⊆S := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    have he := (Finset.mem_filter.mp hi).2
    rw [←he]
    exact hx i
  have hpair : IsClique R (I.image y) := by
    intro a ha b hb hab
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    exact horth i j (fun h => hab (congrArg y h))
  have hc := clique_card_le R S (I.image y) hsub hpair
  simpa [Finset.card_image_of_injective I hy] using hc

theorem replacement_count_bound (R : α → α → Prop) (S : Finset α) {n b : ℕ}
    (x y : Fin b → Fin n → α) (hx : ∀ j i,x j i∈S)
    (hy : ∀ j,Function.Injective (y j))
    (horth : ∀ j i k,i≠k → R (y j i) (y j k)) :
    b*(n-orthogonalityNumber R S)≤
      ∑ j,(Finset.univ.filter fun i => x j i≠y j i).card := by
  classical
  have hper (j : Fin b) : n-orthogonalityNumber R S≤
      (Finset.univ.filter fun i => x j i≠y j i).card := by
    have hc := retained_per_block_le R S (x j) (y j) (hx j) (hy j) (horth j)
    have hcount := Finset.card_filter_add_card_filter_not
      (s:=Finset.univ) (p:=fun i : Fin n => x j i=y j i)
    simp only [Finset.card_univ,Fintype.card_fin] at hcount
    have hcount' : (Finset.univ.filter fun i => x j i=y j i).card+
        (Finset.univ.filter fun i => x j i≠y j i).card=n := by
      simpa only [ne_eq] using hcount
    omega
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hper j)
  simpa using hs


theorem replacement_fraction_bound (R : α → α → Prop) (S : Finset α) {n b : ℕ}
    (hn : 0<n) (x y : Fin b → Fin n → α) (hx : ∀ j i,x j i∈S)
    (hy : ∀ j,Function.Injective (y j))
    (horth : ∀ j i k,i≠k → R (y j i) (y j k)) :
    ((b*n : ℕ) : ℝ)*(1-(orthogonalityNumber R S : ℝ)/n)≤
      ∑ j,((Finset.univ.filter fun i => x j i≠y j i).card : ℝ) := by
  classical
  have hper (j : Fin b) : (n : ℝ)-(orthogonalityNumber R S : ℝ)≤
      ((Finset.univ.filter fun i => x j i≠y j i).card : ℝ) := by
    have hc := retained_per_block_le R S (x j) (y j) (hx j) (hy j) (horth j)
    have hcount := Finset.card_filter_add_card_filter_not
      (s:=Finset.univ) (p:=fun i : Fin n => x j i=y j i)
    simp only [Finset.card_univ,Fintype.card_fin] at hcount
    have hcount' : (Finset.univ.filter fun i => x j i=y j i).card+
        (Finset.univ.filter fun i => x j i≠y j i).card=n := by
      simpa only [ne_eq] using hcount
    have hN : n≤orthogonalityNumber R S+
        (Finset.univ.filter fun i => x j i≠y j i).card := by omega
    have hR : (n : ℝ)≤(orthogonalityNumber R S : ℝ)+
        ((Finset.univ.filter fun i => x j i≠y j i).card : ℝ) := by exact_mod_cast hN
    linarith
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hper j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hnR : (n : ℝ)≠0 := by positivity
  have he : ((b*n : ℕ) : ℝ)*(1-(orthogonalityNumber R S : ℝ)/n)=
      (b : ℝ)*((n : ℝ)-(orthogonalityNumber R S : ℝ)) := by
    push_cast
    field_simp [hnR]
    <;> ring
  rw [he]
  exact hs

def augmentedOrthogonal {d : ℕ} (a b : Fin d → Bool) : Prop :=
  1+(∑ i,bitSign (a i)*bitSign (b i))=0

def hadamardMixtures (d : ℕ) : Set ((Fin d → Bool) → ℝ) :=
  convexHull ℝ (blockLaws (augmentedOrthogonal (d:=d)) (d+1))

theorem hadamard_mixture_support_witness {d : ℕ}
    (S : Finset (Fin d → Bool)) (p : (Fin d → Bool) → ℝ)
    (hp : ∑ x,p x=1) (hsupport : ∀ x,x∉S → p x=0)
    (q : (Fin d → Bool) → ℝ) (hq : q∈hadamardMixtures d) :
    1-(orthogonalityNumber augmentedOrthogonal S : ℝ)/(d+1 : ℕ)≤
      totalVariation p q := by
  exact support_witness_all_mixtures augmentedOrthogonal S (by omega) p hp hsupport q hq


theorem augmentedOrthogonal_self_false {d : ℕ} (a : Fin d → Bool) :
    ¬augmentedOrthogonal a a := by
  intro h
  have hs (i : Fin d) : bitSign (a i)*bitSign (a i)=1 := by
    cases a i <;> rfl
  unfold augmentedOrthogonal at h
  simp_rw [hs] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h
  omega

theorem hadamard_block_replacement_bound {d b : ℕ}
    (S : Finset (Fin d → Bool)) (x y : Fin b → Fin (d+1) → (Fin d → Bool))
    (hx : ∀ j i,x j i∈S)
    (horth : ∀ j i k,i≠k → augmentedOrthogonal (y j i) (y j k)) :
    ((b*(d+1) : ℕ) : ℝ)*
      (1-(orthogonalityNumber augmentedOrthogonal S : ℝ)/(d+1 : ℕ))≤
      ∑ j,((Finset.univ.filter fun i => x j i≠y j i).card : ℝ) := by
  have hy (j : Fin b) : Function.Injective (y j) := by
    intro i k heq
    by_contra hne
    have h := horth j i k hne
    rw [heq] at h
    exact augmentedOrthogonal_self_false _ h
  exact replacement_fraction_bound augmentedOrthogonal S (by omega) x y hx hy horth

end
end EntropyDesigns.SupportWitness
