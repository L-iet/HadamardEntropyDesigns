/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Private draft: not verified or part of the public claim inventory. -/
module
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.SymmDiff
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement

/- For even binary weights a,b, the symmetric-difference identity is
   a+b=c+2*d, where d counts the common ones. These lemmas isolate the
   division and parity step; actual binary-code polarization remains separate. -/
theorem even_symmetric_difference_weight {a b c d : ℕ}
    (ha : a%2=0) (hb : b%2=0) (h : a+b=c+2*d) : c%2=0 := by
  omega

theorem half_weight_polarization {a b c d : ℕ}
    (ha : a%2=0) (hb : b%2=0) (h : a+b=c+2*d) :
    (c/2+d)%2=(a/2+b/2)%2 := by
  omega

theorem balanced_twelve_half_weight : (6/2 : ℕ)%2=1 := by decide

open scoped symmDiff

theorem symmetric_difference_weight {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) :
    s.card+t.card=(s ∆ t).card+2*(s ∩ t).card := by
  have hd : Disjoint (s \ t) (t \ s) := by
    apply Finset.disjoint_left.mpr
    intro x hs ht
    exact (Finset.mem_sdiff.mp hs).2 (Finset.mem_sdiff.mp ht).1
  have hc : (s ∆ t).card=(s \ t).card+(t \ s).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  have hs := Finset.card_sdiff_add_card_inter s t
  have ht := Finset.card_sdiff_add_card_inter t s
  rw [Finset.inter_comm t s] at ht
  omega

theorem even_support_xor {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (hs : s.card%2=0) (ht : t.card%2=0) :
    (s ∆ t).card%2=0 :=
  even_symmetric_difference_weight hs ht (symmetric_difference_weight s t)

theorem support_half_weight_polarization {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (hs : s.card%2=0) (ht : t.card%2=0) :
    ((s ∆ t).card/2+(s ∩ t).card)%2=(s.card/2+t.card/2)%2 :=
  half_weight_polarization hs ht (symmetric_difference_weight s t)

end EntropyDesigns.QuadraticRefinement
