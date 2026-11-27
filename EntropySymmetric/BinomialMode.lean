/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace EntropyDesigns.SymmetricEntropy
noncomputable section
open scoped BigOperators

def binomialTerm (d : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  (Nat.choose d j : ℝ)*p^j*(1-p)^(d-j)

theorem binomialTerm_nonneg (d j : ℕ) {p : ℝ} (hp : 0≤p) (hq : p≤1) :
    0≤binomialTerm d p j := by
  unfold binomialTerm
  positivity

theorem binomialTerm_recurrence (d j : ℕ) (p : ℝ) (hj : j<d) :
    ((j:ℝ)+1)*(1-p)*binomialTerm d p (j+1)=
      ((d:ℝ)-j)*p*binomialTerm d p j := by
  have hc : (Nat.choose d (j+1):ℝ)*((j:ℝ)+1)=
      (Nat.choose d j:ℝ)*((d:ℝ)-j) := by
    have hh := Nat.choose_succ_right_eq d j
    have hhR := congrArg (fun n : ℕ => (n : ℝ)) hh
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub (Nat.le_of_lt hj)] using hhR
  have he : d-j=(d-(j+1))+1 := by omega
  unfold binomialTerm
  rw [he, pow_succ, pow_succ]
  nlinarith [congrArg (fun z : ℝ => z*p^j*(1-p)^(d-(j+1))*p*(1-p)) hc]

theorem binomialTerm_step_up {d k j : ℕ} (hk : k<d) (hj : j<k) :
    binomialTerm d ((k:ℝ)/d) j≤binomialTerm d ((k:ℝ)/d) (j+1) := by
  have hd : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hk' : (k:ℝ)<d := by exact_mod_cast hk
  have hj' : (j:ℝ)+1≤k := by exact_mod_cast hj
  have hp : 0≤(k:ℝ)/d := div_nonneg (Nat.cast_nonneg _) hd.le
  have hq : (k:ℝ)/d<1 := (div_lt_one hd).mpr hk'
  have ha : 0<((j:ℝ)+1)*(1-(k:ℝ)/d) := by positivity
  have hr := binomialTerm_recurrence d j ((k:ℝ)/d) (by omega)
  have hb : ((j:ℝ)+1)*(1-(k:ℝ)/d)≤((d:ℝ)-j)*((k:ℝ)/d) := by
    field_simp
    nlinarith
  have hn := binomialTerm_nonneg d j hp hq.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hb) hn]

theorem binomialTerm_step_down {d k j : ℕ} (hk : k<d) (hj : k≤j) (hjd : j<d) :
    binomialTerm d ((k:ℝ)/d) (j+1)≤binomialTerm d ((k:ℝ)/d) j := by
  have hd : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hk' : (k:ℝ)<d := by exact_mod_cast hk
  have hj' : (k:ℝ)≤j := by exact_mod_cast hj
  have hp : 0≤(k:ℝ)/d := div_nonneg (Nat.cast_nonneg _) hd.le
  have hq : (k:ℝ)/d<1 := (div_lt_one hd).mpr hk'
  have ha : 0<((j:ℝ)+1)*(1-(k:ℝ)/d) := by positivity
  have hr := binomialTerm_recurrence d j ((k:ℝ)/d) hjd
  have hb : ((d:ℝ)-j)*((k:ℝ)/d)≤((j:ℝ)+1)*(1-(k:ℝ)/d) := by
    field_simp
    nlinarith
  have hn := binomialTerm_nonneg d j hp hq.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hb) hn]


theorem binomialTerm_mode {d k j : ℕ} (hk : k<d) (hj : j≤d) :
    binomialTerm d ((k:ℝ)/d) j≤binomialTerm d ((k:ℝ)/d) k := by
  by_cases h : j≤k
  · have hchain : ∀ n, ∀ a, a+n≤k →
        binomialTerm d ((k:ℝ)/d) a≤binomialTerm d ((k:ℝ)/d) (a+n) := by
      intro n
      induction n with
      | zero => intro a _; simp
      | succ n ih =>
        intro a ha
        exact (ih a (by omega)).trans (by
          simpa [Nat.add_assoc] using binomialTerm_step_up hk (show a+n<k by omega))
    have hh := hchain (k-j) j (by omega)
    simpa [Nat.add_sub_of_le h] using hh
  · have hchain : ∀ n, k+n≤d →
        binomialTerm d ((k:ℝ)/d) (k+n)≤binomialTerm d ((k:ℝ)/d) k := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have hs := binomialTerm_step_down hk (show k≤k+n by omega) (show k+n<d by omega)
        have hh := hs.trans (ih (by omega))
        simpa [Nat.add_assoc] using hh
    have hh := hchain (j-k) (by omega)
    simpa [Nat.add_sub_of_le (show k≤j by omega)] using hh

theorem binomialTerm_sum (d : ℕ) (p : ℝ) :
    (∑ j∈Finset.range (d+1),binomialTerm d p j)=1 := by
  have h := add_pow p (1-p) d
  have hs : p+(1-p)=1 := by ring
  rw [hs,one_pow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  unfold binomialTerm
  ring

theorem binomialTerm_mode_lower {d k : ℕ} (hk : k<d) :
    1≤((d:ℝ)+1)*binomialTerm d ((k:ℝ)/d) k := by
  have hh := Finset.sum_le_sum (s:=Finset.range (d+1))
    (fun j hj => binomialTerm_mode hk (show j≤d by have := Finset.mem_range.mp hj; omega))
  simpa [binomialTerm_sum] using hh


theorem log_choose_entropy_interior {d k : ℕ} (hk0 : 0<k) (hk : k<d) :
    (d:ℝ)*Real.binEntropy ((k:ℝ)/d)-Real.log ((d:ℝ)+1)≤Real.log (Nat.choose d k:ℝ) := by
  have hd : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hkR : (0:ℝ)<k := by exact_mod_cast hk0
  have hkd : (k:ℝ)<d := by exact_mod_cast hk
  let p : ℝ := (k:ℝ)/d
  have hp : 0<p := div_pos hkR hd
  have hq : 0<1-p := sub_pos.mpr ((div_lt_one hd).mpr hkd)
  have hC : (0:ℝ)<Nat.choose d k := by exact_mod_cast Nat.choose_pos (Nat.le_of_lt hk)
  have hT : 0<binomialTerm d p k := by unfold binomialTerm; positivity
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<1) (binomialTerm_mode_lower hk)
  rw [Real.log_one,Real.log_mul (by positivity : ((d:ℝ)+1)≠0) hT.ne'] at hl
  have htlog : Real.log (binomialTerm d p k)=Real.log (Nat.choose d k:ℝ)+
      (k:ℝ)*Real.log p+((d:ℝ)-k)*Real.log (1-p) := by
    unfold binomialTerm
    rw [Real.log_mul (mul_pos hC (pow_pos hp _)).ne' (pow_pos hq _).ne',
      Real.log_mul hC.ne' (pow_pos hp _).ne',Real.log_pow,Real.log_pow,
      Nat.cast_sub (Nat.le_of_lt hk)]
  have he : (d:ℝ)*Real.binEntropy p =
      -((k:ℝ)*Real.log p+((d:ℝ)-k)*Real.log (1-p)) := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog_def]
    dsimp [p]
    field_simp
    <;> ring
  change (d:ℝ)*Real.binEntropy p-Real.log ((d:ℝ)+1)≤_
  rw [htlog] at hl
  linarith

theorem log_choose_entropy {d k : ℕ} (hk : k≤d) :
    (d:ℝ)*Real.binEntropy ((k:ℝ)/d)-Real.log ((d:ℝ)+1)≤Real.log (Nat.choose d k:ℝ) := by
  have hl : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  by_cases hk0 : k=0
  · subst k
    simpa using hl
  · by_cases he : k=d
    · subst k
      by_cases hd : d=0
      · subst d; simp
      · have hdR : (d:ℝ)≠0 := by exact_mod_cast hd
        simpa [hdR] using hl
    · exact log_choose_entropy_interior (by omega) (by omega)

end
end EntropyDesigns.SymmetricEntropy
