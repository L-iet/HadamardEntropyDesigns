/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Generic finite-set parity transformations; verification is recorded separately. -/
module
public import EntropyQuadraticClassification.HalfWeightParity
public import Mathlib.Tactic.Tauto
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped symmDiff
variable {ι : Type*} [DecidableEq ι]

def dotParity (s t : Finset ι) : ℕ := (s ∩ t).card%2

def transvection (u s : Finset ι) : Finset ι :=
  if dotParity s u=1 then s ∆ u else s

theorem xor_inter_distrib (s u t : Finset ι) :
    (s ∆ u) ∩ t=(s ∩ t) ∆ (u ∩ t) := by
  ext x
  simp only [Finset.mem_inter,Finset.mem_symmDiff]
  tauto

theorem dotParity_comm (s t : Finset ι) : dotParity s t=dotParity t s := by
  simp [dotParity,Finset.inter_comm]

theorem dotParity_self (s : Finset ι) : dotParity s s=s.card%2 := by
  simp [dotParity]

theorem dotParity_xor_left (s u t : Finset ι) :
    dotParity (s ∆ u) t=(dotParity s t+dotParity u t)%2 := by
  unfold dotParity
  rw [xor_inter_distrib]
  have h := symmetric_difference_weight (s ∩ t) (u ∩ t)
  omega

theorem dotParity_xor_right (s t u : Finset ι) :
    dotParity s (t ∆ u)=(dotParity s t+dotParity s u)%2 := by
  calc
    _=dotParity (t ∆ u) s := dotParity_comm _ _
    _=(dotParity t s+dotParity u s)%2 := dotParity_xor_left _ _ _
    _=_ := by rw [dotParity_comm t s,dotParity_comm u s]

theorem xor_cancel_self_left (s t : Finset ι) : s ∆ (s ∆ t)=t := by
  ext x
  simp only [Finset.mem_symmDiff]
  tauto

theorem xor_preserves_two_mod_four (s u : Finset ι)
    (hs : s.card%4=2) (hu : u.card%4=2) (hodd : dotParity s u=1) :
    (s ∆ u).card%4=2 := by
  have h := symmetric_difference_weight s u
  unfold dotParity at hodd
  omega

theorem transvection_dot (u s t : Finset ι) (hu : u.card%2=0) :
    dotParity (transvection u s) (transvection u t)=dotParity s t := by
  have hst : dotParity s t<2 := Nat.mod_lt _ (by decide)
  have hsu : dotParity s u<2 := Nat.mod_lt _ (by decide)
  have htu : dotParity t u<2 := Nat.mod_lt _ (by decide)
  have hut := dotParity_comm u t
  have huu : dotParity u u=0 := by rw [dotParity_self,hu]
  by_cases hs : dotParity s u=1
  · by_cases ht : dotParity t u=1
    · simp only [transvection,if_pos hs,if_pos ht]
      rw [dotParity_xor_left,dotParity_xor_right,dotParity_xor_right]
      omega
    · simp only [transvection,if_pos hs,if_neg ht]
      rw [dotParity_xor_left]
      omega
  · by_cases ht : dotParity t u=1
    · simp only [transvection,if_neg hs,if_pos ht]
      rw [dotParity_xor_right]
      omega
    · simp only [transvection,if_neg hs,if_neg ht]

theorem transvection_card (u s : Finset ι)
    (hu : u.card%4=2) (hs : s.card%4=2) :
    (transvection u s).card%4=2 := by
  by_cases h : dotParity s u=1
  · simpa only [transvection,if_pos h] using xor_preserves_two_mod_four s u hs hu h
  · simpa only [transvection,if_neg h] using hs

theorem transvection_fixed (u s : Finset ι) (h : dotParity s u=0) :
    transvection u s=s := by simp [transvection,h]

theorem transvection_between_sends (x y : Finset ι)
    (hx : x.card%2=0) (hxy : dotParity x y=1) :
    transvection (x ∆ y) x=y := by
  have h : dotParity x (x ∆ y)=1 := by
    rw [dotParity_xor_right,dotParity_self,hx,hxy]
  simpa only [transvection,if_pos h] using xor_cancel_self_left x y

theorem transvection_between_fixes (p x y : Finset ι)
    (hx : dotParity p x=1) (hy : dotParity p y=1) :
    transvection (x ∆ y) p=p := by
  apply transvection_fixed
  rw [dotParity_xor_right,hx,hy]

end EntropyDesigns.QuadraticRefinement
