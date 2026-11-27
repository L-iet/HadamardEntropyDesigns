/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.Pushforward
public import EntropyDesigns.Collision
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

theorem uniform_fiber_active_bijective {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (f : A → B) (w : A → ℝ) (c : ℝ) (hc : 0<c)
    (hw : ∀ a,0≤w a) (hweights : ∀ a,w a=0 ∨ w a=c)
    (hmarginal : ∀ b,pushLaw f w b=c) :
    Function.Bijective (fun a : {a : A // w a≠0} => f a.val) := by
  classical
  constructor
  · intro x y hxy
    apply Subtype.ext
    by_contra hne
    let g (a : A) := if f a=f x.val then w a else 0
    have hg (a : A) : 0≤g a := by
      unfold g
      split
      · exact hw a
      · exact le_rfl
    have hsum : ∑ a,g a=c := hmarginal (f x.val)
    have hxw : w x.val=c := (hweights x.val).resolve_left x.property
    have hgx : g x.val=c := by simp [g,hxw]
    have hrest : ∑ a∈Finset.univ.erase x.val,g a=0 := by
      have h := Finset.sum_erase_add Finset.univ g (Finset.mem_univ x.val)
      rw [hsum,hgx] at h
      linarith
    have hgy0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hg a)).mp hrest y.val
      (Finset.mem_erase.mpr ⟨(fun h => hne h.symm),Finset.mem_univ y.val⟩)
    have hgy : g y.val=w y.val := by simp [g,hxy]
    exact y.property (hgy.symm.trans hgy0)
  · intro b
    by_contra h
    have hf (a : A) (hab : f a=b) : w a=0 := by
      by_contra ha
      exact h ⟨⟨a,ha⟩,hab⟩
    have hz : pushLaw f w b=0 := by
      unfold pushLaw
      apply Finset.sum_eq_zero
      intro a _
      by_cases hab : f a=b
      · simp [hab,hf a hab]
      · simp [hab]
    have hc0 : c=0 := (hmarginal b).symm.trans hz
    exact (ne_of_gt hc) hc0
end
end EntropyDesigns.SupportFace
