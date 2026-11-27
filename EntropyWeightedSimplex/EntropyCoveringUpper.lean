/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyWeightedSimplex.EntropyCountLimits
@[expose] public section
namespace EntropyDesigns.WeightedSimplex
open Filter
open scoped BigOperators Topology Classical

noncomputable def entropyLinearConstant {r : ℕ} (b : Fin r → ℕ) : ℝ :=
  1+(r:ℝ)*Real.log ((r:ℝ)-1)-Real.log (simplexDenominator b)

noncomputable def firstUnrepresented {r : ℕ} (b : Fin r → ℕ) (m : ℕ) : ℕ :=
  sInf {n : ℕ | 0<n ∧ ¬HadamardMultibase.SumOfAtMost (HadamardMultibase.powerMonoid b) m n}

noncomputable def coveringTrialOrder {r : ℕ} (b : Fin r → ℕ) (η : ℝ) (m : ℕ) : ℕ :=
  entropyTrialOrder ((r:ℝ)-1) (r:ℝ) (entropyLinearConstant b+η/2) m

noncomputable def normalizedCoveringRemainder {r : ℕ} (b : Fin r → ℕ) (m : ℕ) : ℝ :=
  (Real.log (firstUnrepresented b m:ℝ)-((r:ℝ)-1)*(m:ℝ)*Real.log m-
    (r:ℝ)*(m:ℝ)*Real.log (Real.log m))/(m:ℝ)

 theorem first_unrepresented_spec {r : ℕ} (b : Fin r → ℕ) (hb : ∀ i,2≤b i) (m : ℕ) :
    0<firstUnrepresented b m ∧
      ¬HadamardMultibase.SumOfAtMost (HadamardMultibase.powerMonoid b) m (firstUnrepresented b m) :=
  Nat.sInf_mem (HadamardMultibase.hasMissing_powerMonoid hb m)

 theorem first_unrepresented_le_missing {r : ℕ} (b : Fin r → ℕ) (m n : ℕ)
    (hn : 0<n) (hmiss : ¬HadamardMultibase.SumOfAtMost (HadamardMultibase.powerMonoid b) m n) :
    firstUnrepresented b m≤n := Nat.sInf_le ⟨hn,hmiss⟩

 theorem entropy_trial_choose_lt_order {r : ℕ} (hr : 2≤r) (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) (η : ℝ) (hη : 0<η) :
    ∀ᶠ m : ℕ in atTop,
      ((HadamardMultibase.truncatedMonoid b (coveringTrialOrder b η m)).card+m).choose m<
        coveringTrialOrder b η m := by
  let a : ℝ := (r:ℝ)-1
  let d : ℝ := entropyLinearConstant b+η/2
  have ha : 0<a := by
    have hR : (2:ℝ)≤r := by exact_mod_cast hr
    dsimp [a]
    linarith
  have hα := entropy_trial_log_alphabet_upper hr b hb hind a r d (η/4) ha (by positivity)
  have hN := entropy_trial_log_order_bounds a r d ha
  filter_upwards [hα,hN,eventually_ge_atTop (1:ℕ)] with m hα hN hm
  let N := entropyTrialOrder a r d m
  let U := (HadamardMultibase.truncatedMonoid b N).card
  have hmpos : 0<m := by omega
  have hmR : (0:ℝ)<m := by exact_mod_cast hmpos
  have hchoose := HadamardMultibase.log_choose_add_le U hmpos
  have hgap : Real.log (((U+m).choose m:ℕ):ℝ)<Real.log (N:ℝ) := by
    calc
      _≤(m:ℝ)*(1+Real.log ((U+m:ℕ):ℝ)-Real.log m) := by simpa only [Nat.cast_add] using hchoose
      _≤(m:ℝ)*(1+((r:ℝ)*Real.log m+(r:ℝ)*Real.log (Real.log m)+
          (r:ℝ)*Real.log a-Real.log (simplexDenominator b)+η/4)-Real.log m) :=
        mul_le_mul_of_nonneg_left (by linarith) hmR.le
      _=entropyTrialExponent a r (entropyLinearConstant b+η/4) m := by
        dsimp [entropyTrialExponent,entropyLinearConstant,a]
        ring
      _<entropyTrialExponent a r d m := by
        dsimp [entropyTrialExponent,d]
        nlinarith [mul_pos hη hmR]
      _≤Real.log (N:ℝ) := hN.1
  have hpC : (0:ℝ)<(((U+m).choose m:ℕ):ℝ) := by
    exact_mod_cast Nat.choose_pos (show m≤U+m by omega)
  have hpN : (0:ℝ)<N := by exact_mod_cast entropy_trial_order_positive a r d m
  have hnat : (U+m).choose m<N := by
    exact_mod_cast (Real.log_lt_log_iff hpC hpN).mp hgap
  exact hnat

 theorem second_order_covering_upper {r : ℕ} (hr : 2≤r) (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) (η : ℝ) (hη : 0<η) :
    ∀ᶠ m : ℕ in atTop,Real.log (firstUnrepresented b m:ℝ)≤
      ((r:ℝ)-1)*(m:ℝ)*Real.log m+(r:ℝ)*(m:ℝ)*Real.log (Real.log m)+
        (entropyLinearConstant b+η)*(m:ℝ) := by
  let a : ℝ := (r:ℝ)-1
  let d : ℝ := entropyLinearConstant b+η/2
  have ha : 0<a := by
    have hR : (2:ℝ)≤r := by exact_mod_cast hr
    dsimp [a]
    linarith
  have hchoose := entropy_trial_choose_lt_order hr b hb hind η hη
  have hN := entropy_trial_log_order_bounds a r d ha
  filter_upwards [hchoose,hN,eventually_ge_atTop (⌈2*Real.log (2:ℝ)/η⌉₊),
    eventually_ge_atTop (1:ℕ)] with m hchoose hN hmargin hm
  let N := coveringTrialOrder b η m
  obtain ⟨n,hn,hnN,hnot⟩ := HadamardMultibase.exists_missing_powerMonoid_of_count hb hchoose
  have hfirst : firstUnrepresented b m≤N :=
    (first_unrepresented_le_missing b m n (by omega) hnot).trans hnN
  have hfirstpos : (0:ℝ)<firstUnrepresented b m := by exact_mod_cast (first_unrepresented_spec b hb m).1
  have hlogle : Real.log (firstUnrepresented b m:ℝ)≤Real.log (N:ℝ) :=
    Real.log_le_log hfirstpos (by exact_mod_cast hfirst)
  have hceil := Nat.le_ceil (2*Real.log (2:ℝ)/η)
  have hmR : (⌈2*Real.log (2:ℝ)/η⌉₊:ℝ)≤m := by exact_mod_cast hmargin
  have hmul := (div_le_iff₀ hη).mp (hceil.trans hmR)
  calc
    _≤Real.log (N:ℝ) := hlogle
    _≤entropyTrialExponent a r d m+Real.log 2 := hN.2
    _≤_ := by
      dsimp [entropyTrialExponent,a,d]
      nlinarith

 theorem normalized_covering_remainder_eventual_upper {r : ℕ} (hr : 2≤r)
    (b : Fin r → ℕ) (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b)
    (η : ℝ) (hη : 0<η) :
    ∀ᶠ m : ℕ in atTop,normalizedCoveringRemainder b m≤entropyLinearConstant b+η := by
  filter_upwards [second_order_covering_upper hr b hb hind η hη,
    eventually_ge_atTop (1:ℕ)] with m hm hmpos
  have hmR : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  apply (div_le_iff₀ hmR).mpr
  linarith

end EntropyDesigns.WeightedSimplex
