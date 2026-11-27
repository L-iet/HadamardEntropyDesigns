/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Block complements preserve the stated parity conditions. Exact real Gram
conditions are a separate obligation in the quadratic-code application. -/
module
public import EntropyQuadraticClassification.Transvections
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped symmDiff
variable {ι : Type*} [DecidableEq ι]

def SatisfiesChecks (checks : Finset (Finset ι)) (s : Finset ι) : Prop :=
  ∀ M∈checks,dotParity s M=0

def blockNormalize (u : Finset ι) (a : ι) (s : Finset ι) : Finset ι :=
  if a∈s then s ∆ u else s

theorem checks_xor {checks : Finset (Finset ι)} {s u : Finset ι}
    (hs : SatisfiesChecks checks s) (hu : SatisfiesChecks checks u) :
    SatisfiesChecks checks (s ∆ u) := by
  intro M hM
  simp only [dotParity_xor_left,hs M hM,hu M hM]

theorem checks_transvection {checks : Finset (Finset ι)} {s u : Finset ι}
    (hs : SatisfiesChecks checks s) (hu : SatisfiesChecks checks u) :
    SatisfiesChecks checks (transvection u s) := by
  by_cases h : dotParity s u=1
  · simpa only [transvection,if_pos h] using checks_xor hs hu
  · simpa only [transvection,if_neg h] using hs

theorem xor_card_radical (s u : Finset ι)
    (hu : u.card%4=0) (hsu : dotParity s u=0) :
    (s ∆ u).card%4=s.card%4 := by
  have h := symmetric_difference_weight s u
  unfold dotParity at hsu
  omega

theorem xor_dot_left_zero (s u t : Finset ι) (hut : dotParity u t=0) :
    dotParity (s ∆ u) t=dotParity s t := by
  have hst : dotParity s t<2 := Nat.mod_lt _ (by decide)
  rw [dotParity_xor_left,hut]
  omega

theorem xor_dot_right_zero (s t u : Finset ι) (hsu : dotParity s u=0) :
    dotParity s (t ∆ u)=dotParity s t := by
  have hst : dotParity s t<2 := Nat.mod_lt _ (by decide)
  rw [dotParity_xor_right,hsu]
  omega

theorem blockNormalize_card (u s : Finset ι) (a : ι)
    (hu : u.card%4=0) (hsu : dotParity s u=0) :
    (blockNormalize u a s).card%4=s.card%4 := by
  by_cases h : a∈s
  · simpa only [blockNormalize,if_pos h] using xor_card_radical s u hu hsu
  · simp only [blockNormalize,if_neg h]

theorem blockNormalize_checks {checks : Finset (Finset ι)} {s u : Finset ι}
    (a : ι) (hs : SatisfiesChecks checks s) (hu : SatisfiesChecks checks u) :
    SatisfiesChecks checks (blockNormalize u a s) := by
  by_cases h : a∈s
  · simpa only [blockNormalize,if_pos h] using checks_xor hs hu
  · simpa only [blockNormalize,if_neg h] using hs

theorem blockNormalize_first (u s : Finset ι) (a : ι) (ha : a∈u) :
    a∉blockNormalize u a s := by
  by_cases h : a∈s <;> simp [blockNormalize,h,Finset.mem_symmDiff,ha]

theorem blockNormalize_fixed (u s : Finset ι) (a : ι) (ha : a∉s) :
    blockNormalize u a s=s := by simp [blockNormalize,ha]

theorem blockNormalize_membership_off (u s : Finset ι) (a b : ι) (hb : b∉u) :
    b∈blockNormalize u a s ↔ b∈s := by
  by_cases h : a∈s <;> simp [blockNormalize,h,Finset.mem_symmDiff,hb]

theorem blockNormalize_dot (u s t : Finset ι) (a : ι)
    (hu : u.card%2=0) (hsu : dotParity s u=0) (htu : dotParity t u=0) :
    dotParity (blockNormalize u a s) (blockNormalize u a t)=dotParity s t := by
  have hut : dotParity u t=0 := (dotParity_comm u t).trans htu
  have huu : dotParity u u=0 := by rw [dotParity_self,hu]
  have hst : dotParity s t<2 := Nat.mod_lt _ (by decide)
  by_cases hs : a∈s
  · by_cases ht : a∈t
    · simp only [blockNormalize,if_pos hs,if_pos ht]
      rw [dotParity_xor_left,dotParity_xor_right,dotParity_xor_right]
      omega
    · simpa only [blockNormalize,if_pos hs,if_neg ht] using xor_dot_left_zero s u t hut
  · by_cases ht : a∈t
    · simpa only [blockNormalize,if_neg hs,if_pos ht] using xor_dot_right_zero s t u hsu
    · simp only [blockNormalize,if_neg hs,if_neg ht]

end EntropyDesigns.QuadraticRefinement
