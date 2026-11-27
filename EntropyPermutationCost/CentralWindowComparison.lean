/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPermutationCost.SymmetricRunBounds
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.FieldSimp
@[expose] public section
namespace EntropyDesigns.PermutationCost

 theorem central_weight_quarter_lower {d k : ℕ} (hd : 16≤d)
    (hk : IsCentralWeight d k) : (d:ℝ)≤4*((k:ℝ)+1) := by
  have hdR : (16:ℝ)≤d := by exact_mod_cast hd
  have hsq := hk.2
  have hp := mul_nonneg (sub_nonneg.mpr hdR) (Nat.cast_nonneg d (α:=ℝ))
  by_contra h
  have hlt : 4*((k:ℝ)+1)<d := lt_of_not_ge h
  have hx : (d:ℝ)/2<d-2*(k:ℝ) := by linarith
  have hn := mul_nonneg (sub_nonneg.mpr hx.le) (show (0:ℝ)≤d/2 by positivity)
  nlinarith [sq_nonneg ((d:ℝ)-2*(k:ℝ)-(d:ℝ)/2)]

 theorem central_window_choose_comparison {d k : ℕ} (hd : 16≤d)
    (hk : IsCentralWeight d k) (hmid : k≤d/2) :
    (d.choose (d/2):ℝ)≤Real.exp 2*(d.choose k:ℝ) := by
  let a : ℝ := ((d:ℝ)-2*(k:ℝ))/((k:ℝ)+1)
  have hden : (0:ℝ)<(k:ℝ)+1 := by positivity
  have htwo : 2*k≤d := by omega
  have hx : (0:ℝ)≤(d:ℝ)-2*(k:ℝ) := by
    have ht : (2:ℝ)*(k:ℝ)≤(d:ℝ) := by exact_mod_cast htwo
    exact sub_nonneg.mpr ht
  have ha : 0≤a := div_nonneg hx hden.le
  have had : a*((k:ℝ)+1)=(d:ℝ)-2*(k:ℝ) := div_mul_cancel₀ _ hden.ne'
  have hstep (j : ℕ) (hkj : k≤j) (hjd : j<d/2) :
      (d.choose (j+1):ℝ)≤Real.exp a*(d.choose j:ℝ) := by
    have hjd' : j≤d := by omega
    have hrec : (d.choose (j+1):ℝ)*((j:ℝ)+1)=
        (d.choose j:ℝ)*((d:ℝ)-(j:ℝ)) := by
      exact_mod_cast Nat.choose_succ_right_eq d j
    have hkjR : (k:ℝ)≤j := by exact_mod_cast hkj
    have hjpos : (0:ℝ)<(j:ℝ)+1 := by positivity
    have hm := mul_nonneg ha (sub_nonneg.mpr hkjR)
    have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp a) hjpos.le
    have hv : (d:ℝ)-(j:ℝ)≤Real.exp a*((j:ℝ)+1) := by nlinarith
    have hb := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg (d.choose j) (α:=ℝ))
    nlinarith
  have hiter : ∀ r : ℕ,k+r≤d/2 →
      (d.choose (k+r):ℝ)≤Real.exp (a*(r:ℝ))*(d.choose k:ℝ) := by
    intro r
    induction r with
    | zero => intro _;simp
    | succ r ih =>
      intro hr
      have hp := ih (by omega)
      have hs := hstep (k+r) (by omega) (by omega)
      calc
        _=(d.choose (k+r+1):ℝ) := by congr 2 <;> omega
        _≤Real.exp a*(d.choose (k+r):ℝ) := hs
        _≤Real.exp a*(Real.exp (a*(r:ℝ))*(d.choose k:ℝ)) :=
          mul_le_mul_of_nonneg_left hp (Real.exp_pos a).le
        _=Real.exp (a*((r+1:ℕ):ℝ))*(d.choose k:ℝ) := by
          rw [←mul_assoc,←Real.exp_add]
          congr 1
          push_cast
          ring
  let r := d/2-k
  have hr : k+r=d/2 := by dsimp [r];omega
  have hiter' := hiter r (by omega)
  rw [hr] at hiter'
  have hquarter := central_weight_quarter_lower hd hk
  have hrR : 2*(r:ℝ)≤(d:ℝ)-2*(k:ℝ) := by
    have h : 2*r≤d-2*k := by dsimp [r];omega
    exact_mod_cast h
  have hprod := mul_le_mul_of_nonneg_left hrR hx
  have hsq := hk.2
  have har : a*(r:ℝ)≤2 := by
    change (((d:ℝ)-2*(k:ℝ))/((k:ℝ)+1))*(r:ℝ)≤2
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact hiter'.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr har)
    (Nat.cast_nonneg (d.choose k) (α:=ℝ)))

 theorem least_central_weight_le_middle (d : ℕ) : leastCentralWeight d≤d/2 := by
  have hs := least_central_weight_spec d
  have hh := least_central_weight_le (central_weight_reflection hs)
  omega

 theorem symmetric_run_count_central_binomial_bounds {d : ℕ} (hd : 16≤d) :
    (Nat.centralBinom (d/2):ℝ)≤Real.exp 2*(symmetricRunCount d:ℝ) ∧
    (symmetricRunCount d:ℝ)≤2*(Nat.centralBinom (d/2):ℝ) := by
  obtain ⟨hlo,hup⟩ := symmetric_run_count_exact_bounds (show 2≤d by omega)
  have hcmp := central_window_choose_comparison hd (least_central_weight_spec d)
    (least_central_weight_le_middle d)
  have hbase : Nat.centralBinom (d/2)≤d.choose (d/2) :=
    Nat.choose_le_choose _ (show 2*(d/2)≤d by omega)
  have hloR : (d.choose (leastCentralWeight d):ℝ)≤symmetricRunCount d := by exact_mod_cast hlo
  constructor
  · exact (show (Nat.centralBinom (d/2):ℝ)≤(d.choose (d/2):ℝ) by exact_mod_cast hbase).trans
      (hcmp.trans (mul_le_mul_of_nonneg_left hloR (Real.exp_pos 2).le))
  · exact_mod_cast hup

end EntropyDesigns.PermutationCost
