/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyWeightedSimplex.RecursiveSimplexCount
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.SetTheory.Cardinal.Finite
@[expose] public section
namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Classical

noncomputable def SimplexChoices : List ℝ → ℝ → Type
  | [], L => {u : Unit // 0≤L}
  | c::cs, L => (a : Fin (⌊L/c⌋₊+1)) × SimplexChoices cs (L-c*(a.val:ℝ))

noncomputable instance simplexChoicesFintype (cs : List ℝ) (L : ℝ) :
    Fintype (SimplexChoices cs L) := by
  induction cs generalizing L with
  | nil => change Fintype {u : Unit // 0≤L};infer_instance
  | cons c cs ih =>
    change Fintype ((a : Fin (⌊L/c⌋₊+1)) × SimplexChoices cs (L-c*(a.val:ℝ)))
    letI (a : Fin (⌊L/c⌋₊+1)) : Fintype (SimplexChoices cs (L-c*(a.val:ℝ))) := ih _
    infer_instance

 theorem simplex_choices_card (cs : List ℝ) (L : ℝ) :
    Fintype.card (SimplexChoices cs L)=simplexCount cs L := by
  induction cs generalizing L with
  | nil => by_cases hL : 0≤L <;> simp [SimplexChoices,simplexCount,hL]
  | cons c cs ih =>
    change Fintype.card ((a : Fin (⌊L/c⌋₊+1)) × SimplexChoices cs (L-c*(a.val:ℝ)))=_
    rw [Fintype.card_sigma]
    simp_rw [ih]
    rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => simplexCount cs (L-c*(a:ℝ)))]
    rfl

 def weightedExponentSum (cs : List ℝ) (a : Fin cs.length → ℕ) : ℝ :=
  ∑ i,cs.get i*(a i:ℝ)

 theorem weighted_exponent_sum_cons (c : ℝ) (cs : List ℝ)
    (a : Fin (c::cs).length → ℕ) :
    weightedExponentSum (c::cs) a=c*(a 0:ℝ)+weightedExponentSum cs (Fin.tail a) := by
  simp [weightedExponentSum,Fin.sum_univ_succ,Fin.tail]

 theorem weighted_exponent_sum_nonnegative (cs : List ℝ) (hc : ∀ c∈cs,0<c)
    (a : Fin cs.length → ℕ) : 0≤weightedExponentSum cs a := by
  induction cs with
  | nil => simp [weightedExponentSum]
  | cons c cs ih =>
    rw [weighted_exponent_sum_cons]
    exact add_nonneg (mul_nonneg (hc c (by simp)).le (Nat.cast_nonneg _))
      (ih (fun x hx => hc x (by simp [hx])) (Fin.tail a))

noncomputable def choiceTuple : (cs : List ℝ) → (L : ℝ) →
    SimplexChoices cs L → (Fin cs.length → ℕ)
  | [], _, _ => Fin.elim0
  | c::cs, L, q => Fin.cons q.1.val (choiceTuple cs (L-c*(q.1.val:ℝ)) q.2)

 theorem choice_tuple_weight_bound (cs : List ℝ) (L : ℝ) (q : SimplexChoices cs L) :
    weightedExponentSum cs (choiceTuple cs L q)≤L := by
  induction cs generalizing L with
  | nil => simpa [weightedExponentSum] using q.property
  | cons c cs ih =>
    obtain ⟨a,q⟩ := q
    have hh := ih (L-c*(a.val:ℝ)) q
    rw [weighted_exponent_sum_cons]
    change c*(a.val:ℝ)+weightedExponentSum cs (choiceTuple cs (L-c*(a.val:ℝ)) q)≤L
    linarith

 theorem choice_tuple_injective (cs : List ℝ) (L : ℝ) :
    Function.Injective (choiceTuple cs L) := by
  induction cs generalizing L with
  | nil =>
    intro x y _
    apply Subtype.ext
    exact Subsingleton.elim x.val y.val
  | cons c cs ih =>
    intro x y he
    obtain ⟨a,x⟩ := x
    obtain ⟨b,y⟩ := y
    have hab : a.val=b.val := by simpa only [choiceTuple,Fin.cons_zero] using congrFun he 0
    have hab' : a=b := Fin.ext hab
    subst b
    have ht : choiceTuple cs (L-c*(a.val:ℝ)) x=choiceTuple cs (L-c*(a.val:ℝ)) y := by
      funext i
      simpa only [choiceTuple,Fin.cons_succ] using congrFun he i.succ
    have hxy := ih (L-c*(a.val:ℝ)) ht
    subst y
    rfl

end EntropyDesigns.WeightedSimplex
