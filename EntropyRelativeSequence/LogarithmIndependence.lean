/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
The generic logarithm lemma is reused from the same-author Apache-2.0
HadamardMultibase.GeneralIndependence; exact source and notice provenance
is recorded in owned-logarithm-lemma-provenance.json. The2,12 specialization
and valuation proof below are original here. -/
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.RelativeSequence
noncomputable section

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

@[simp] private theorem val_two_two : padicValRat 2 2=1 :=
  (padicValRat.of_nat (p:=2) (n:=2)).trans
    (by norm_num [padicValNat,Nat.maxPowDvdDiv,Nat.maxPowDvdDiv.go])
@[simp] private theorem val_two_twelve : padicValRat 2 12=2 :=
  (padicValRat.of_nat (p:=2) (n:=12)).trans
    (by norm_num [padicValNat,Nat.maxPowDvdDiv,Nat.maxPowDvdDiv.go])
@[simp] private theorem val_three_two : padicValRat 3 2=0 :=
  (padicValRat.of_nat (p:=3) (n:=2)).trans
    (by norm_num [padicValNat,Nat.maxPowDvdDiv,Nat.maxPowDvdDiv.go])
@[simp] private theorem val_three_twelve : padicValRat 3 12=1 :=
  (padicValRat.of_nat (p:=3) (n:=12)).trans
    (by norm_num [padicValNat,Nat.maxPowDvdDiv,Nat.maxPowDvdDiv.go])

theorem independent_two_twelve (a b : ℤ) (h : (2:ℚ)^a*12^b=1) : a=0 ∧ b=0 := by
  have h2 := congrArg (padicValRat 2) h
  have h3 := congrArg (padicValRat 3) h
  rw [padicValRat.mul (by positivity) (by positivity)] at h2 h3
  simp only [padicValRat.zpow,val_two_two,val_two_twelve,val_three_two,val_three_twelve,
    padicValRat.one,mul_one,mul_zero,zero_add,add_zero] at h2 h3
  exact ⟨by omega,h3⟩

theorem irrational_log_ratio_of_independent_pair {p q : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hind : ∀ a c : ℤ, (p : ℚ) ^ a * (q : ℚ) ^ c = 1 → a = 0 ∧ c = 0) :
    Irrational (Real.log (q : ℝ) / Real.log (p : ℝ)) := by
  rw [irrational_iff_ne_rational]
  intro a c hc heq
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hcross := (div_eq_div_iff hlogp.ne' hcR).mp heq
  have hlogs : Real.log ((q : ℝ) ^ c) = Real.log ((p : ℝ) ^ a) := by
    rw [Real.log_zpow, Real.log_zpow]
    nlinarith
  have hpowers : (q : ℝ) ^ c = (p : ℝ) ^ a :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (zpow_pos hq0 _))
      (Set.mem_Ioi.mpr (zpow_pos hp0 _)) hlogs
  have hpowersQ : (q : ℚ) ^ c = (p : ℚ) ^ a := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact hpowers
  have hpQ : (p : ℚ) ≠ 0 := by positivity
  have hrel : (p : ℚ) ^ (-a) * (q : ℚ) ^ c = 1 := by
    rw [zpow_neg, hpowersQ, inv_mul_cancel₀ (zpow_ne_zero _ hpQ)]
  exact hc (hind (-a) c hrel).2

theorem irrational_log_twelve_div_log_two : Irrational (Real.log (12:ℝ)/Real.log (2:ℝ)) := by
  exact irrational_log_ratio_of_independent_pair (by decide : 2≤(2:ℕ))
    (by decide : 2≤(12:ℕ)) independent_two_twelve

end
end EntropyDesigns.RelativeSequence
