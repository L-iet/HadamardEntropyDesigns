/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
Modified imports for bounded compilation; mathematical statements and proof bodies are unchanged. -/
module
public import Mathlib.Data.Fintype.BigOperators
public import EntropyDesigns.WeightedKernels
public import EntropyDesigns.ExactExtraction
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.NoncommRing
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FunProp
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Field
@[expose] public section
set_option maxHeartbeats 2000000
namespace EntropyDesigns
open scoped BigOperators
noncomputable section

def graphBilinear {α : Type*} [Fintype α] (R : α → α → Prop) (p q : α → ℝ) : ℝ := by
  classical
  exact ∑ a,∑ b,if R a b then p a*q b else 0

def graphEdgeMass {α : Type*} [Fintype α] (R : α → α → Prop) (w : α → ℝ) : ℝ := graphBilinear R w w

def graphNeighborMass {α : Type*} [Fintype α] (R : α → α → Prop) (w : α → ℝ) (a : α) : ℝ := by
  classical
  exact ∑ b,if R a b then w b else 0

def mergeDirection {α : Type*} [DecidableEq α] (x y : α) : α → ℝ := fun a => (if a=x then 1 else 0)-(if a=y then 1 else 0)

theorem graphBilinear_add_left {α : Type*} [Fintype α] (R : α → α → Prop) (p q r : α → ℝ) :
    graphBilinear R (p+q) r=graphBilinear R p r+graphBilinear R q r := by
  classical
  simp only [graphBilinear,Pi.add_apply,add_mul,ite_add_zero,Finset.sum_add_distrib]

theorem graphBilinear_smul_left {α : Type*} [Fintype α] (R : α → α → Prop) (t : ℝ) (p q : α → ℝ) :
    graphBilinear R (t • p) q=t*graphBilinear R p q := by
  classical
  simp only [graphBilinear,Pi.smul_apply,smul_eq_mul,mul_assoc,mul_ite,mul_zero,Finset.mul_sum]

theorem graphBilinear_symmetric {α : Type*} [Fintype α] (R : α → α → Prop)
    (hR : Symmetric R) (p q : α → ℝ) : graphBilinear R p q=graphBilinear R q p := by
  classical
  rw [graphBilinear,graphBilinear,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : R a b
  · simp [hab,hR hab,mul_comm]
  · have hba : ¬R b a := fun h => hab (hR h)
    simp [hab,hba]

theorem graphBilinear_mergeDirection {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) (w : α → ℝ) (x y : α) :
    graphBilinear R (mergeDirection x y) w=graphNeighborMass R w x-graphNeighborMass R w y := by
  classical
  have hd (P : Prop) [Decidable P] (u v : ℝ) :
      (if P then u-v else 0)=(if P then u else 0)-(if P then v else 0) := by
    by_cases h : P <;> simp [h]
  simp only [graphBilinear,mergeDirection,sub_mul,ite_mul,one_mul,zero_mul,hd,
    Finset.sum_sub_distrib]
  have ht (a b z : α) : (if R a b then (if a=z then w b else 0) else 0)=
      (if a=z then (if R a b then w b else 0) else 0) := by
    by_cases h : R a b <;> by_cases hz : a=z <;> simp [h,hz]
  simp_rw [ht]
  simp [graphNeighborMass]


theorem graphBilinear_add_right {α : Type*} [Fintype α] (R : α → α → Prop)
    (hR : Symmetric R) (p q r : α → ℝ) :
    graphBilinear R p (q+r)=graphBilinear R p q+graphBilinear R p r := by
  rw [graphBilinear_symmetric R hR p (q+r),graphBilinear_add_left]
  rw [graphBilinear_symmetric R hR q p,graphBilinear_symmetric R hR r p]

theorem graphBilinear_smul_right {α : Type*} [Fintype α] (R : α → α → Prop)
    (hR : Symmetric R) (t : ℝ) (p q : α → ℝ) :
    graphBilinear R p (t • q)=t*graphBilinear R p q := by
  rw [graphBilinear_symmetric R hR p (t • q),graphBilinear_smul_left,graphBilinear_symmetric R hR q p]

theorem mergeDirection_edge_zero {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) (hR : Symmetric R) (hIr : ∀ a,¬R a a)
    (x y : α) (hxy : ¬R x y) : graphBilinear R (mergeDirection x y) (mergeDirection x y)=0 := by
  classical
  have hNeighbor (a : α) (ha : a=x ∨ a=y) : graphNeighborMass R (mergeDirection x y) a=0 := by
    unfold graphNeighborMass
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hab : R a b
    · have hbx : b≠x := by
        intro h;subst b
        rcases ha with rfl|rfl
        · exact hIr _ hab
        · exact hxy (hR hab)
      have hby : b≠y := by
        intro h;subst b
        rcases ha with rfl|rfl
        · exact hxy hab
        · exact hIr _ hab
      simp [hab,mergeDirection,hbx,hby]
    · simp [hab]
  rw [graphBilinear_mergeDirection,hNeighbor x (Or.inl rfl),hNeighbor y (Or.inr rfl),sub_self]

theorem graphEdgeMass_merge_formula {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) (hR : Symmetric R) (hIr : ∀ a,¬R a a)
    (w : α → ℝ) (x y : α) (hxy : ¬R x y) (t : ℝ) :
    graphEdgeMass R (w+t • mergeDirection x y)=graphEdgeMass R w+
      2*t*(graphNeighborMass R w x-graphNeighborMass R w y) := by
  unfold graphEdgeMass
  simp only [graphBilinear_add_left,graphBilinear_add_right R hR,graphBilinear_smul_left,graphBilinear_smul_right R hR]
  rw [mergeDirection_edge_zero R hR hIr x y hxy,
    graphBilinear_symmetric R hR w (mergeDirection x y),graphBilinear_mergeDirection]
  ring

def mergedWeights {α : Type*} [DecidableEq α] (w : α → ℝ) (x y : α) : α → ℝ := w+w y • mergeDirection x y

def positiveGraphSupport {α : Type*} [Fintype α] (w : α → ℝ) : Finset α := by
  classical
  exact Finset.univ.filter (fun a => 0<w a)

theorem mergedWeights_values {α : Type*} [DecidableEq α] (w : α → ℝ) (x y : α) (hxy : x≠y) :
    mergedWeights w x y x=w x+w y ∧ mergedWeights w x y y=0 ∧
      ∀ a,a≠x → a≠y → mergedWeights w x y a=w a := by
  refine ⟨by simp [mergedWeights,mergeDirection,hxy],by simp [mergedWeights,mergeDirection,Ne.symm hxy],?_⟩
  intro a hax hay
  simp [mergedWeights,mergeDirection,hax,hay]

theorem mergedWeights_step {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) (hR : Symmetric R) (hIr : ∀ a,¬R a a)
    (w : α → ℝ) (hw : ∀ a,0≤w a) (x y : α) (hx : 0<w x) (hy : 0<w y)
    (hxy : x≠y) (hNon : ¬R x y) (hNeighbor : graphNeighborMass R w y≤graphNeighborMass R w x) :
    (∀ a,0≤mergedWeights w x y a) ∧ (∑ a,mergedWeights w x y a)=∑ a,w a ∧
      graphEdgeMass R w≤graphEdgeMass R (mergedWeights w x y) ∧
      positiveGraphSupport (mergedWeights w x y)=(positiveGraphSupport w).erase y := by
  classical
  obtain ⟨hMx,hMy,hMo⟩ := mergedWeights_values w x y hxy
  refine ⟨?_,?_,?_,?_⟩
  · intro a
    by_cases hax : a=x
    · subst a;rw [hMx];positivity
    · by_cases hay : a=y
      · subst a;rw [hMy]
      · rw [hMo a hax hay];exact hw a
  · change (∑ a : α,(w a+w y*mergeDirection x y a))=(∑ a : α,w a)
    rw [Finset.sum_add_distrib,← Finset.mul_sum]
    have hD : (∑ a,mergeDirection x y a)=0 := by simp [mergeDirection,Finset.sum_sub_distrib]
    rw [hD,mul_zero,add_zero]
  · rw [mergedWeights,graphEdgeMass_merge_formula R hR hIr w x y hNon]
    nlinarith
  · ext a
    simp only [positiveGraphSupport,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
    by_cases hax : a=x
    · subst a;rw [hMx];simp [hxy,hx,show 0<w x+w y by linarith]
    · by_cases hay : a=y
      · subst a;rw [hMy];simp
      · rw [hMo a hax hay];simp [hay]


def graphMergeStep {α : Type*} [Fintype α] [DecidableEq α] (R : α → α → Prop)
    (w q : α → ℝ) : Prop :=
  ∃ x y,0<w x ∧ 0<w y ∧ x≠y ∧ ¬R x y ∧
    graphNeighborMass R w y≤graphNeighborMass R w x ∧ q=mergedWeights w x y

def hasCliqueSupport {α : Type*} [Fintype α] (R : α → α → Prop) (w : α → ℝ) : Prop :=
  ∀ x∈positiveGraphSupport w,∀ y∈positiveGraphSupport w,x≠y → R x y

theorem graph_merge_reduction {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) (hR : Symmetric R) (hIr : ∀ a,¬R a a)
    (w : α → ℝ) (hw : ∀ a,0≤w a) (hNot : ¬hasCliqueSupport R w) :
    ∃ q : α → ℝ,graphMergeStep R w q ∧ (∀ a,0≤q a) ∧
      (∑ a,q a)=∑ a,w a ∧ graphEdgeMass R w≤graphEdgeMass R q ∧
      positiveGraphSupport q⊆positiveGraphSupport w ∧
      (positiveGraphSupport q).card<(positiveGraphSupport w).card := by
  classical
  unfold hasCliqueSupport at hNot
  push_neg at hNot
  obtain ⟨x,hx,y,hy,hxy,hNon⟩ := hNot
  have hx' : 0<w x := (Finset.mem_filter.mp hx).2
  have hy' : 0<w y := (Finset.mem_filter.mp hy).2
  have hDo (a b : α) (ha : 0<w a) (hb : 0<w b) (hab : a≠b)
      (hN : ¬R a b) (hScore : graphNeighborMass R w b≤graphNeighborMass R w a) :
      ∃ q : α → ℝ,graphMergeStep R w q ∧ (∀ a,0≤q a) ∧
        (∑ a,q a)=∑ a,w a ∧ graphEdgeMass R w≤graphEdgeMass R q ∧
        positiveGraphSupport q⊆positiveGraphSupport w ∧
        (positiveGraphSupport q).card<(positiveGraphSupport w).card := by
    obtain ⟨hPos,hSum,hEdge,hSupp⟩ := mergedWeights_step R hR hIr w hw a b ha hb hab hN hScore
    refine ⟨mergedWeights w a b,⟨a,b,ha,hb,hab,hN,hScore,rfl⟩,hPos,hSum,hEdge,?_,?_⟩
    · rw [hSupp];exact Finset.erase_subset _ _
    · rw [hSupp]
      exact Finset.card_erase_lt_of_mem (by simp [positiveGraphSupport,hb])
  by_cases hScore : graphNeighborMass R w y≤graphNeighborMass R w x
  · exact hDo x y hx' hy' hxy hNon hScore
  · exact hDo y x hy' hx' (Ne.symm hxy) (fun h => hNon (hR h)) (le_of_not_ge hScore)

theorem finite_weight_merging {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) (hR : Symmetric R) (hIr : ∀ a,¬R a a)
    (w : α → ℝ) (hw : ∀ a,0≤w a) :
    ∃ q : α → ℝ,(∀ a,0≤q a) ∧ (∑ a,q a)=∑ a,w a ∧
      graphEdgeMass R w≤graphEdgeMass R q ∧ positiveGraphSupport q⊆positiveGraphSupport w ∧
      hasCliqueSupport R q ∧ Relation.ReflTransGen (graphMergeStep R) w q := by
  classical
  have aux (k : ℕ) : ∀ p : α → ℝ,(∀ a,0≤p a) → (positiveGraphSupport p).card=k →
      ∃ q : α → ℝ,(∀ a,0≤q a) ∧ (∑ a,q a)=∑ a,p a ∧
        graphEdgeMass R p≤graphEdgeMass R q ∧ positiveGraphSupport q⊆positiveGraphSupport p ∧
        hasCliqueSupport R q ∧ Relation.ReflTransGen (graphMergeStep R) p q := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro p hp hk
      by_cases hC : hasCliqueSupport R p
      · exact ⟨p,hp,rfl,le_rfl,Finset.Subset.refl _,hC,Relation.ReflTransGen.refl⟩
      · obtain ⟨v,hStep,hv,hSum,hEdge,hSubset,hCard⟩ := graph_merge_reduction R hR hIr p hp hC
        obtain ⟨q,hq,hqSum,hqEdge,hqSubset,hqClique,hqReach⟩ := ih (positiveGraphSupport v).card
          (by omega) v hv rfl
        refine ⟨q,hq,hqSum.trans hSum,hEdge.trans hqEdge,hqSubset.trans hSubset,hqClique,?_⟩
        exact (Relation.ReflTransGen.single hStep).trans hqReach
  exact aux _ w hw rfl



theorem clique_edge_mass_formula {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) (hIr : ∀ a,¬R a a) (q : α → ℝ)
    (hq : ∀ a,0≤q a) (hmass : ∑ a,q a=1) (hClique : hasCliqueSupport R q) :
    graphEdgeMass R q=1-∑ a,q a^2 := by
  classical
  have hp (a b : α) : (if R a b then q a*q b else 0)=q a*q b-(if a=b then q a^2 else 0) := by
    by_cases hab : a=b
    · subst b;simp [hIr a,pow_two]
    · by_cases ha : q a=0
      · simp [ha,hab]
      · by_cases hb : q b=0
        · simp [hb,hab]
        · have hRa : a∈positiveGraphSupport q := by simp [positiveGraphSupport,lt_of_le_of_ne (hq a) (Ne.symm ha)]
          have hRb : b∈positiveGraphSupport q := by simp [positiveGraphSupport,lt_of_le_of_ne (hq b) (Ne.symm hb)]
          simp [hClique a hRa b hRb hab,hab]
  unfold graphEdgeMass graphBilinear
  simp_rw [hp,Finset.sum_sub_distrib]
  simp [← Finset.mul_sum,hmass]

theorem probability_support_cauchy {α : Type*} [Fintype α] [DecidableEq α]
    (q : α → ℝ) (hq : ∀ a,0≤q a) (hmass : ∑ a,q a=1) :
    1≤((positiveGraphSupport q).card : ℝ)*(∑ a,q a^2) := by
  classical
  let S := positiveGraphSupport q
  have hOutside (a : α) (ha : a∉S) : q a=0 := by
    have hn : ¬0<q a := by simpa [S,positiveGraphSupport] using ha
    linarith [hq a]
  have hSum : ∑ a∈S,q a=1 := by
    rw [← hmass]
    exact Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hOutside a ha)
  have hSq : ∑ a∈S,q a^2=∑ a,q a^2 := by
    exact Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => by rw [hOutside a ha];ring)
  have hC := Finset.sum_mul_sq_le_sq_mul_sq S q (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,hSum,hSq,one_pow] at hC
  nlinarith

theorem weighted_clique_extraction {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) (hR : Symmetric R) (hIr : ∀ a,¬R a a)
    (w : α → ℝ) (hw : ∀ a,0≤w a) (hmass : ∑ a,w a=1)
    (n : ℕ) (hn : 2≤n) (hEdge : 1-1/((n : ℝ)-1)<graphEdgeMass R w) :
    ∃ q : α → ℝ,(∀ a,0≤q a) ∧ (∑ a,q a)=1 ∧
      positiveGraphSupport q⊆positiveGraphSupport w ∧ hasCliqueSupport R q ∧
      n≤(positiveGraphSupport q).card ∧ Relation.ReflTransGen (graphMergeStep R) w q := by
  classical
  obtain ⟨q,hq,hqSum,hqEdge,hqSubset,hqClique,hqReach⟩ := finite_weight_merging R hR hIr w hw
  have hMass : ∑ a,q a=1 := hqSum.trans hmass
  refine ⟨q,hq,hMass,hqSubset,hqClique,?_,hqReach⟩
  have hN : 0<(n : ℝ)-1 := by exact_mod_cast (show 0<(n : ℤ)-1 by omega)
  have hCauchy := probability_support_cauchy q hq hMass
  have hFormula := clique_edge_mass_formula R hIr q hq hMass hqClique
  have hSq : 0≤∑ a,q a^2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  by_contra hCard
  have hCard' : ((positiveGraphSupport q).card : ℝ)≤(n : ℝ)-1 := by
    exact_mod_cast (show ((positiveGraphSupport q).card : ℤ)≤(n : ℤ)-1 by omega)
  have hSmall : ∑ a,q a^2<1/((n : ℝ)-1) := by linarith
  have hProd := (lt_div_iff₀ hN).mp hSmall
  have hBound := mul_le_mul_of_nonneg_right hCard' hSq
  nlinarith



theorem graph_energy_lower_bound {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) (hIr : ∀ a,¬R a a) (w : α → ℝ)
    (hw : ∀ a,0≤w a) (hmass : ∑ a,w a=1) (P : α → α → ℝ) (D a : ℝ)
    (hP : ∀ x y,0≤P x y) (hDiag : ∀ x,P x x=D)
    (hGap : ∀ x y,0<w x → 0<w y → x≠y → ¬R x y → a^2≤P x y) :
    a^2*(1-graphEdgeMass R w)+(D-a^2)*collision w≤weightedTotal w P := by
  classical
  have hp (x y : α) : a^2*(w x*w y-(if R x y then w x*w y else 0))+
      (D-a^2)*(if x=y then w x^2 else 0)≤w x*w y*P x y := by
    by_cases hxy : x=y
    · subst y;simp only [hIr x,ite_false,ite_true,hDiag];nlinarith
    · simp only [hxy,ite_false,mul_zero,add_zero]
      by_cases hRxy : R x y
      · simp only [hRxy,ite_true,sub_self,mul_zero]
        exact mul_nonneg (mul_nonneg (hw x) (hw y)) (hP x y)
      · simp only [hRxy,ite_false,sub_zero]
        by_cases hx : w x=0
        · simp [hx]
        · by_cases hy : w y=0
          · simp [hy]
          · have hg := hGap x y (lt_of_le_of_ne (hw x) (Ne.symm hx))
              (lt_of_le_of_ne (hw y) (Ne.symm hy)) hxy hRxy
            nlinarith [mul_nonneg (mul_nonneg (hw x) (hw y)) (sub_nonneg.mpr hg)]
  have hSum := Finset.sum_le_sum fun x (_ : x∈Finset.univ) => Finset.sum_le_sum fun y (_ : y∈Finset.univ) => hp x y
  have hMassPair : (∑ x,∑ y,w x*w y)=1 := by
    simp only [← Finset.mul_sum,hmass,mul_one]
  simpa only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true,hMassPair,hmass,mul_one,graphEdgeMass,graphBilinear,collision,weightedTotal] using hSum

theorem energy_collision_clique_certificate {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) (hR : Symmetric R) (hIr : ∀ x,¬R x x)
    (w : α → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (P : α → α → ℝ) (n : ℕ) (hn : 2≤n) (a E : ℝ) (ha : 0<a)
    (hP : ∀ x y,0≤P x y) (hDiag : ∀ x,P x x=(n : ℝ)^2)
    (hGap : ∀ x y,0<w x → 0<w y → x≠y → ¬R x y → a^2≤P x y)
    (hTotal : weightedTotal w P=(n : ℝ)+E)
    (hCert : ((n : ℝ)^2-a^2)*collision w>(n : ℝ)+E-a^2/((n : ℝ)-1)) :
    ∃ q : α → ℝ,(∀ x,0≤q x) ∧ (∑ x,q x)=1 ∧
      positiveGraphSupport q⊆positiveGraphSupport w ∧ hasCliqueSupport R q ∧
      n≤(positiveGraphSupport q).card ∧ Relation.ReflTransGen (graphMergeStep R) w q := by
  have hLow := graph_energy_lower_bound R hIr w hw hmass P ((n : ℝ)^2) a hP hDiag hGap
  rw [hTotal] at hLow
  have hPos : 0<a^2 := sq_pos_of_pos ha
  have hd : a^2/((n : ℝ)-1)=a^2*(1/((n : ℝ)-1)) := by ring
  rw [hd] at hCert
  apply weighted_clique_extraction R hR hIr w hw hmass n hn
  nlinarith



def signMomentMatrix {α ι : Type*} [Fintype α] (v : α → ι → ℝ) (w : α → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∑ a,w a*v a i*v a j

def signMomentError {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (v : α → ι → ℝ) (w : α → ℝ) : ℝ := ∑ i,∑ j,(signMomentMatrix v w i j-(1 : Matrix ι ι ℝ) i j)^2

theorem sign_moment_energy_identity {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (v : α → ι → ℝ) (w : α → ℝ) (hsign : ∀ a i,v a i=1 ∨ v a i= -1)
    (hmass : ∑ a,w a=1) :
    weightedTotal w (fun a b => inner v a b^2)=(Fintype.card ι : ℝ)+signMomentError v w := by
  classical
  have hTrace : weightedTotal w (fun a b => inner v a b^2)=∑ i,∑ j,signMomentMatrix v w i j^2 := by
    unfold weightedTotal inner
    calc
      (∑ a,∑ b,w a*w b*(∑ i,v a i*v b i)^2)=
          ∑ a,∑ b,∑ i,∑ j,w a*w b*(v a i*v b i)*(v a j*v b j) := by
        simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl;intro a ha
        apply Finset.sum_congr rfl;intro b hb
        apply Finset.sum_congr rfl;intro i hi
        apply Finset.sum_congr rfl;intro j hj
        ring
      _=∑ a,∑ i,∑ j,∑ b,w a*w b*(v a i*v b i)*(v a j*v b j) := by
        apply Finset.sum_congr rfl;intro a ha
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl;intro i hi
        rw [Finset.sum_comm]
      _=∑ i,∑ j,∑ a,∑ b,w a*w b*(v a i*v b i)*(v a j*v b j) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl;intro i hi
        rw [Finset.sum_comm]
      _=_ := by
        simp only [signMomentMatrix,pow_two,Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl;intro i hi
        apply Finset.sum_congr rfl;intro j hj
        apply Finset.sum_congr rfl;intro a ha
        apply Finset.sum_congr rfl;intro b hb
        ring
  have hDiag (i : ι) : signMomentMatrix v w i i=1 := by
    unfold signMomentMatrix
    convert hmass using 1
    apply Finset.sum_congr rfl
    intro a ha
    rcases hsign a i with h|h <;> rw [h] <;> ring
  have hEntry (i j : ι) : signMomentMatrix v w i j^2=
      (signMomentMatrix v w i j-(1 : Matrix ι ι ℝ) i j)^2+(1 : Matrix ι ι ℝ) i j := by
    by_cases hij : i=j
    · subst j;simp [hDiag,Matrix.one_apply]
    · simp [Matrix.one_apply,hij]
  rw [hTrace]
  simp_rw [hEntry,Finset.sum_add_distrib]
  simp [signMomentError,Matrix.one_apply,add_comm]



theorem clique_sign_rows_hadamard {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (hn : 0<n) (v : α → Fin n → ℝ) (hsign : ∀ a i,v a i=1 ∨ v a i= -1)
    (S : Finset α) (hCard : n≤S.card)
    (hOrth : ∀ a∈S,∀ b∈S,a≠b → inner v a b=0) :
    ∃ rows : Fin n ↪ α,(∀ i,rows i∈S) ∧
      Matrix.IsHadamard (fun i j => v (rows i) j : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  obtain ⟨T,hTS,hTcard⟩ := Finset.exists_subset_card_eq hCard
  let e : Fin n ≃ ↥T := Fintype.equivOfCardEq (by simp only [Fintype.card_fin,Fintype.card_coe,hTcard])
  let rows : Fin n ↪ α := ⟨fun i => (e i).val,fun i j h => e.injective (Subtype.ext h)⟩
  have hRows (i : Fin n) : rows i∈S := hTS (e i).property
  let H : Matrix (Fin n) (Fin n) ℝ := fun i j => v (rows i) j
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hGram : H*H.transpose=(n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    change (∑ k : Fin n,v (rows i) k*v (rows j) k)=(n : ℝ)*(if i=j then 1 else 0)
    by_cases hij : i=j
    · subst j
      have hs (k : Fin n) : v (rows i) k*v (rows i) k=1 := by
        rcases hsign (rows i) k with h|h <;> rw [h] <;> norm_num
      simp [hs]
    · simpa only [inner,hij,ite_false,mul_zero] using hOrth (rows i) (hRows i) (rows j) (hRows j)
        (fun h => hij (rows.injective h))
  refine ⟨rows,hRows,?_⟩
  exact EntropyDesigns.Completion.isHadamard_mathlib ⟨(fun i j => hsign (rows i) j),by simpa only [Fintype.card_fin] using hGram⟩

theorem collision_moment_sign_certificate {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (hn : 2≤n) (v : α → Fin n → ℝ) (hsign : ∀ x i,v x i=1 ∨ v x i= -1)
    (w : α → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1) (a : ℝ) (ha : 0<a)
    (hGap : ∀ x y,0<w x → 0<w y → x≠y → inner v x y≠0 → a^2 ≤ inner v x y^2)
    (hCert : ((n : ℝ)^2-a^2)*collision w>(n : ℝ)+signMomentError v w-a^2/((n : ℝ)-1)) :
    ∃ (q : α → ℝ) (rows : Fin n ↪ α),
      (∀ x,0≤q x) ∧ (∑ x,q x)=1 ∧ positiveGraphSupport q⊆positiveGraphSupport w ∧
      hasCliqueSupport (fun x y => inner v x y=0) q ∧
      Relation.ReflTransGen (graphMergeStep (fun x y => inner v x y=0)) w q ∧
      (∀ i,rows i∈positiveGraphSupport q) ∧
      Matrix.IsHadamard (fun i j => v (rows i) j : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  have hDiag (x : α) : inner v x x=(n : ℝ) := by
    unfold inner
    have hx (i : Fin n) : v x i*v x i=1 := by rcases hsign x i with h|h <;> rw [h] <;> norm_num
    simp [hx]
  have hSym : Symmetric (fun x y => inner v x y=0) := by
    intro x y h
    simpa only [inner,mul_comm] using h
  have hIr : ∀ x,¬inner v x x=0 := by
    intro x;rw [hDiag];exact_mod_cast (show n≠0 by omega)
  obtain ⟨q,hq,hqMass,hSubset,hClique,hCard,hReach⟩ := energy_collision_clique_certificate
    (fun x y => inner v x y=0) hSym hIr w hw hmass (fun x y => inner v x y^2) n hn a
    (signMomentError v w) ha (fun _ _ => sq_nonneg _) (fun x => by rw [hDiag]) hGap
    (by simpa only [Fintype.card_fin] using sign_moment_energy_identity v w hsign hmass) hCert
  obtain ⟨rows,hRows,hHad⟩ := clique_sign_rows_hadamard (by omega) v hsign (positiveGraphSupport q) hCard hClique
  exact ⟨q,rows,hq,hqMass,hSubset,hClique,hReach,hRows,hHad⟩



theorem even_integer_sign_inner_gap {α : Type*} {n : ℕ} (hn : n%2=0)
    (A : α → Fin n → ℤ) (hA : ∀ x i,A x i=1 ∨ A x i= -1) (x y : α)
    (hNZ : inner (fun x i => (A x i : ℝ)) x y≠0) :
    (2 : ℝ)^2 ≤ inner (fun x i => (A x i : ℝ)) x y^2 := by
  let f : Fin n → ℤ := fun i => A x i*A y i
  have hf (i : Fin n) (_ : i∈Finset.univ) : f i=1 ∨ f i= -1 := by
    rcases hA x i with h|h <;> rcases hA y i with h'|h' <;> simp [f,h,h']
  have h4 := sign_sum_mod_four Finset.univ f hf
  have hp := prod_sign Finset.univ f hf
  have hEven : (∑ i,f i)%2=0 := by
    simp only [Finset.card_univ,Fintype.card_fin] at h4
    have hn' : (n : ℤ)%2=0 := by omega
    rcases hp with hp|hp <;> rw [hp] at h4 <;> omega
  have hCast : ((∑ i,f i : ℤ) : ℝ)=inner (fun x i => (A x i : ℝ)) x y := by
    simp [inner,f]
  have hNZ' : (∑ i,f i)≠0 := by intro h;apply hNZ;rw [← hCast,h];norm_num
  have hh : (∑ i,f i)≤ -2 ∨ 2≤(∑ i,f i) := by omega
  have hSq : (4 : ℤ)≤(∑ i,f i)^2 := by rcases hh with h|h <;> nlinarith
  rw [← hCast]
  exact_mod_cast hSq

theorem same_parity_integer_sign_inner_gap {α : Type*} {n : ℕ} (hn : n%4=0)
    (A : α → Fin n → ℤ) (hA : ∀ x i,A x i=1 ∨ A x i= -1) (x y : α)
    (hParity : (∏ i,A x i)=(∏ i,A y i))
    (hNZ : inner (fun x i => (A x i : ℝ)) x y≠0) :
    (4 : ℝ)^2 ≤ inner (fun x i => (A x i : ℝ)) x y^2 := by
  let f : Fin n → ℤ := fun i => A x i*A y i
  have hf (i : Fin n) (_ : i∈Finset.univ) : f i=1 ∨ f i= -1 := by
    rcases hA x i with h|h <;> rcases hA y i with h'|h' <;> simp [f,h,h']
  have hpX := prod_sign Finset.univ (A x) (fun i _ => hA x i)
  have hp : (∏ i,f i)=1 := by
    simp only [f,Finset.prod_mul_distrib,hParity]
    rcases hpX with h|h <;> rw [hParity] at h <;> rw [h] <;> norm_num
  have h4 := sign_sum_mod_four Finset.univ f hf
  simp only [Finset.card_univ,Fintype.card_fin,hp,sub_add_cancel] at h4
  have hMod : (∑ i,f i)%4=0 := by omega
  have hCast : ((∑ i,f i : ℤ) : ℝ)=inner (fun x i => (A x i : ℝ)) x y := by simp [inner,f]
  have hNZ' : (∑ i,f i)≠0 := by intro h;apply hNZ;rw [← hCast,h];norm_num
  have hh : (∑ i,f i)≤ -4 ∨ 4≤(∑ i,f i) := by omega
  have hSq : (16 : ℤ)≤(∑ i,f i)^2 := by rcases hh with h|h <;> nlinarith
  rw [← hCast]
  exact_mod_cast hSq

theorem even_sign_collision_rounding {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (hn : 4≤n) (hEven : n%2=0) (A : α → Fin n → ℤ) (hA : ∀ x i,A x i=1 ∨ A x i= -1)
    (w : α → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hCert : ((n : ℝ)^2-4)*collision w>(n : ℝ)+signMomentError (fun x i => (A x i : ℝ)) w-4/((n : ℝ)-1)) :
    ∃ rows : Fin n ↪ α,(∀ i,0<w (rows i)) ∧
      Matrix.IsHadamard (fun i j => (A (rows i) j : ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
  have hSign : ∀ x i,(A x i : ℝ)=1 ∨ (A x i : ℝ)= -1 := by
    intro x i;rcases hA x i with h|h <;> simp [h]
  obtain ⟨q,rows,hq,hMass,hSubset,hClique,hReach,hRows,hHad⟩ := collision_moment_sign_certificate
    (by omega) (fun x i => (A x i : ℝ)) hSign w hw hmass 2 (by norm_num)
    (fun x y _ _ _ hNZ => even_integer_sign_inner_gap hEven A hA x y hNZ) (by norm_num at hCert ⊢;exact hCert)
  refine ⟨rows,?_,hHad⟩
  intro i
  exact (Finset.mem_filter.mp (hSubset (hRows i))).2



theorem single_parity_collision_rounding {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (hn : 4<n) (hFour : n%4=0) (A : α → Fin n → ℤ) (hA : ∀ x i,A x i=1 ∨ A x i= -1)
    (w : α → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hParity : ∀ x y,0<w x → 0<w y → (∏ i,A x i)=(∏ i,A y i))
    (hCert : ((n : ℝ)^2-16)*collision w>(n : ℝ)+signMomentError (fun x i => (A x i : ℝ)) w-16/((n : ℝ)-1)) :
    ∃ rows : Fin n ↪ α,(∀ i,0<w (rows i)) ∧
      Matrix.IsHadamard (fun i j => (A (rows i) j : ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
  have hSign : ∀ x i,(A x i : ℝ)=1 ∨ (A x i : ℝ)= -1 := by
    intro x i;rcases hA x i with h|h <;> simp [h]
  obtain ⟨q,rows,hq,hMass,hSubset,hClique,hReach,hRows,hHad⟩ := collision_moment_sign_certificate
    (by omega) (fun x i => (A x i : ℝ)) hSign w hw hmass 4 (by norm_num)
    (fun x y hx hy _ hNZ => same_parity_integer_sign_inner_gap hFour A hA x y (hParity x y hx hy) hNZ)
    (by norm_num at hCert ⊢;exact hCert)
  refine ⟨rows,?_,hHad⟩
  intro i
  exact (Finset.mem_filter.mp (hSubset (hRows i))).2

theorem signMomentError_zero_of_isotropic {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (v : α → ι → ℝ) (w : α → ℝ)
    (hiso : ∀ i j,∑ x,w x*v x i*v x j=if i=j then 1 else 0) : signMomentError v w=0 := by
  simp [signMomentError,signMomentMatrix,hiso,Matrix.one_apply]

theorem collision_threshold_algebra (n a : ℝ) (hn : 1<n) (ha : 0<a) (han : a<n) :
    (n^2-a^2)*(1/n-a^2/(n*(n-1)*(n^2-a^2)))=n-a^2/(n-1) := by
  have hn0 : n≠0 := by linarith
  have hn1 : n-1≠0 := by linarith
  have hD : n^2-a^2≠0 := by nlinarith
  field_simp
  <;> ring

theorem exact_moment_collision_gap {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (hn : 2≤n) (v : α → Fin n → ℝ) (hsign : ∀ x i,v x i=1 ∨ v x i= -1)
    (w : α → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hiso : ∀ i j,∑ x,w x*v x i*v x j=if i=j then 1 else 0)
    (a : ℝ) (ha : 0<a) (han : a<n)
    (hGap : ∀ x y,0<w x → 0<w y → x≠y → inner v x y≠0 → a^2 ≤ inner v x y^2) :
    (1/(n : ℝ)-a^2/((n : ℝ)*((n : ℝ)-1)*((n : ℝ)^2-a^2))<collision w →
      ∃ rows : Fin n ↪ α,(∀ i,0<w (rows i)) ∧
        Matrix.IsHadamard (fun i j => v (rows i) j : Matrix (Fin n) (Fin n) ℝ)) ∧
    (¬(∃ H : Matrix (Fin n) (Fin n) ℝ,Matrix.IsHadamard H) →
      collision w≤1/(n : ℝ)-a^2/((n : ℝ)*((n : ℝ)-1)*((n : ℝ)^2-a^2))) := by
  classical
  have hExtract (hC : 1/(n : ℝ)-a^2/((n : ℝ)*((n : ℝ)-1)*((n : ℝ)^2-a^2))<collision w) :
      ∃ rows : Fin n ↪ α,(∀ i,0<w (rows i)) ∧
        Matrix.IsHadamard (fun i j => v (rows i) j : Matrix (Fin n) (Fin n) ℝ) := by
    have hnR : (1 : ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hPos : 0<(n : ℝ)^2-a^2 := by nlinarith
    have hCert := mul_lt_mul_of_pos_left hC hPos
    rw [collision_threshold_algebra (n : ℝ) a hnR ha han] at hCert
    have hE := signMomentError_zero_of_isotropic v w hiso
    obtain ⟨q,rows,hq,hMass,hSubset,hClique,hReach,hRows,hHad⟩ := collision_moment_sign_certificate
      hn v hsign w hw hmass a ha hGap (by simpa only [hE,add_zero] using hCert)
    refine ⟨rows,?_,hHad⟩
    intro i;exact (Finset.mem_filter.mp (hSubset (hRows i))).2
  refine ⟨hExtract,?_⟩
  intro hNo
  by_contra hC
  obtain ⟨rows,hRows,hHad⟩ := hExtract (lt_of_not_ge hC)
  exact hNo ⟨_,hHad⟩



def HasSupportedHadamard {α : Type*} [Fintype α] {n : ℕ}
    (A : α → Fin n → ℤ) (w : α → ℝ) : Prop :=
  ∃ rows : Fin n ↪ α,(∀ i,0<w (rows i)) ∧
    Matrix.IsHadamard (fun i j => (A (rows i) j : ℝ) : Matrix (Fin n) (Fin n) ℝ)

theorem explicit_collision_gap {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (hn : 4≤n) (hEven : n%2=0) (A : α → Fin n → ℤ) (hA : ∀ x i,A x i=1 ∨ A x i= -1)
    (w : α → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hiso : ∀ i j,∑ x,w x*(A x i : ℝ)*(A x j : ℝ)=if i=j then 1 else 0) :
    let c2 := 1/(n : ℝ)-4/((n : ℝ)*((n : ℝ)-1)*((n : ℝ)^2-4))
    (c2<collision w → HasSupportedHadamard A w) ∧
    (¬(∃ H : Matrix (Fin n) (Fin n) ℝ,Matrix.IsHadamard H) → collision w≤c2) ∧
    (4<n → n%4=0 → (∀ x y,0<w x → 0<w y → (∏ i,A x i)=(∏ i,A y i)) →
      let c4 := 1/(n : ℝ)-16/((n : ℝ)*((n : ℝ)-1)*((n : ℝ)^2-16))
      (c4<collision w → HasSupportedHadamard A w) ∧
      (¬(∃ H : Matrix (Fin n) (Fin n) ℝ,Matrix.IsHadamard H) → collision w≤c4)) := by
  have hSign : ∀ x i,(A x i : ℝ)=1 ∨ (A x i : ℝ)= -1 := by
    intro x i;rcases hA x i with h|h <;> simp [h]
  have h2 := exact_moment_collision_gap (by omega) (fun x i => (A x i : ℝ)) hSign w hw hmass hiso
    2 (by norm_num) (by exact_mod_cast (show 2<n by omega))
    (fun x y _ _ _ hNZ => even_integer_sign_inner_gap hEven A hA x y hNZ)
  dsimp only
  refine ⟨by simpa only [HasSupportedHadamard,show (2 : ℝ)^2=4 by norm_num] using h2.1,
    by simpa only [show (2 : ℝ)^2=4 by norm_num] using h2.2,?_⟩
  intro hn4 hFour hParity
  have h4 := exact_moment_collision_gap (by omega) (fun x i => (A x i : ℝ)) hSign w hw hmass hiso
    4 (by norm_num) (by exact_mod_cast hn4)
    (fun x y hx hy _ hNZ => same_parity_integer_sign_inner_gap hFour A hA x y (hParity x y hx hy) hNZ)
  simpa only [HasSupportedHadamard,show (4 : ℝ)^2=16 by norm_num] using h4


end
end EntropyDesigns
