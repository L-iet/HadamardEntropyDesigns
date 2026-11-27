/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Character
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

def boolSupportEquiv (r : ℕ) : (Fin r → Bool) ≃ Finset (Fin r) where
  toFun := boolCoordinateSupport
  invFun S := fun i => decide (i∈S)
  left_inv x := by
    funext i
    cases hx : x i <;> simp [boolCoordinateSupport,hx]
  right_inv S := by
    ext i
    simp [boolCoordinateSupport]

theorem affine_boolean_sign_sum {r : ℕ} (g : Finset (Fin r) → ZMod 2)
    (hg : g∈lowDegreeBooleanCode r 1) :
    (∑ z : Finset (Fin r),booleanValueSign (g z))=0 ∨
    (∑ z : Finset (Fin r),booleanValueSign (g z))=(2 : ℤ)^r ∨
    (∑ z : Finset (Fin r),booleanValueSign (g z))= -(2 : ℤ)^r := by
  obtain ⟨ε,S,hε,hrep⟩ := degree_one_boolean_sign_character g hg
  have heq : (∑ z : Finset (Fin r),booleanValueSign (g z))=
      ε*∑ x : Fin r → Bool,walshChar S x := by
    calc
      _=∑ x : Fin r → Bool,booleanValueSign (g (boolCoordinateSupport x)) :=
        (Equiv.sum_comp (boolSupportEquiv r) (fun z => booleanValueSign (g z))).symm
      _=ε*∑ x : Fin r → Bool,walshChar S x := by
        simp_rw [hrep]
        rw [Finset.mul_sum]
  rw [heq]
  by_cases hs : S=∅
  · rcases hε with hε|hε <;> simp [hs,hε,walshChar,Fintype.card_fun]
  · left
    rw [walshChar_sum_zero S (Finset.nonempty_iff_ne_empty.mpr hs),mul_zero]

def booleanSupportIndicator {r : ℕ} (S : Finset (Finset (Fin r))) (z : Finset (Fin r)) : ZMod 2 :=
  if z∈S then 1 else 0

theorem booleanSupportIndicator_sign_sum {r : ℕ} (S : Finset (Finset (Fin r))) :
    (∑ z : Finset (Fin r),booleanValueSign (booleanSupportIndicator S z))=
      (2 : ℤ)^r-2*(S.card : ℤ) := by
  classical
  have hpoint (z : Finset (Fin r)) : booleanValueSign (booleanSupportIndicator S z)=
      1-2*(if z∈S then (1 : ℤ) else 0) := by
    by_cases hz : z∈S <;> norm_num [booleanValueSign,booleanSupportIndicator,hz]
  have hcount : (∑ z : Finset (Fin r),if z∈S then (1 : ℤ) else 0)=(S.card : ℤ) := by
    have hfilter : Finset.univ.filter (fun z : Finset (Fin r) => z∈S)=S := by ext z; simp
    rw [←Finset.sum_filter,hfilter]
    simp
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,hcount]
  simp [Fintype.card_finset,Fintype.card_fin]

theorem twelve_label_indicator_not_affine (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    booleanSupportIndicator S ∉ lowDegreeBooleanCode 4 1 := by
  intro hg
  have hh := affine_boolean_sign_sum (booleanSupportIndicator S) hg
  rw [booleanSupportIndicator_sign_sum,hS] at hh
  norm_num at hh

end
end EntropyDesigns
