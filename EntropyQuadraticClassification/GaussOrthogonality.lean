/- Copyright (c) 2026 Joshua Mark. Apache-2.0. -/
module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped BigOperators

 theorem sum_zero_of_negating_equiv {A : Type*} [Fintype A]
    (e : A ≃ A) (f : A → ℤ) (h : ∀ x, f (e x) = -f x) :
    ∑ x, f x = 0 := by
  have he := e.sum_comp f
  have hn : (∑ x, f (e x)) = -∑ x, f x := by
    simp only [h, Finset.sum_neg_distrib]
  omega

 theorem sign_character_sum {A : Type*} [AddGroup A] [Fintype A]
    (f : A → ℤ) (hm : ∀ x y, f (x+y)=f x*f y)
    (hu : ∀ x, f x=1 ∨ f x= -1) :
    (∑ x, f x) = if ∀ x, f x=1 then (Fintype.card A : ℤ) else 0 := by
  classical
  split_ifs with h
  · simp [h]
  · obtain ⟨w,hw⟩ := not_forall.mp h
    have hn : f w= -1 := (hu w).resolve_left hw
    apply sum_zero_of_negating_equiv (Equiv.addRight w) f
    intro x
    change f (x+w)= -f x
    simp [hm,hn]

 theorem shift_sum {A : Type*} [AddGroup A] [Fintype A]
    (f : A → ℤ) (w : A) : (∑ x, f (x+w))=∑ x, f x :=
  Equiv.sum_comp (Equiv.addRight w) f

 theorem isotropic_orthogonal_gauss {V : Type*} [AddCommGroup V] [Fintype V]
    (W : AddSubgroup V) [Fintype W] (s : V → ℤ) (b : V → W → ℤ)
    (hm : ∀ x u v, b x (u+v)=b x u*b x v)
    (hu : ∀ x w, b x w=1 ∨ b x w= -1)
    (hq : ∀ x (w : W), s (x+(w:V))=s x*b x w) :
    (∑ x, s x) = ∑ x, if ∀ w, b x w=1 then s x else 0 := by
  classical
  have h : (Fintype.card W : ℤ)*(∑ x, s x) =
      (Fintype.card W : ℤ)*(∑ x, if ∀ w, b x w=1 then s x else 0) := by
    calc
      _ = ∑ w : W, ∑ x : V, s (x+(w:V)) := by
        simp only [shift_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ x : V, s x*(∑ w : W, b x w) := by
        rw [Finset.sum_comm]
        simp only [hq, Finset.mul_sum]
      _ = _ := by
        simp_rw [sign_character_sum _ (hm _) (hu _)]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        split_ifs <;> simp_all [mul_comm]
  have hp : (0:ℤ)<Fintype.card W := by exact_mod_cast Fintype.card_pos
  exact mul_left_cancel₀ (ne_of_gt hp) h

end EntropyDesigns.QuadraticRefinement
