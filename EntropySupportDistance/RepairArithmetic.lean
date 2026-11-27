/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SharpDistance
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section

theorem repair_offset_divisibility {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) : k∣(2^s)^(k-1) := by
  have hkh : k≤2^s := by omega
  have hpowle : (2:ℕ)^r≤2^s := by simpa only [←hkpow] using hkh
  have hrs : r≤s := (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hpowle
  have hex : r≤s*(k-1) := by
    have hk1 : 1≤k-1 := by omega
    nlinarith
  have hd := pow_dvd_pow (2:ℕ) hex
  rw [pow_mul] at hd
  simpa only [←hkpow] using hd

theorem repair_exact_block_budget {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) :
    (k*2^s)*((2^s)^(k-1)/k)=(2^s)^k ∧
      (2^s)^k/(k*2^s)=(2^s)^(k-1)/k ∧
      (2^s)^(k-1)/k≤(2^s)^(k-1) := by
  have hdiv := repair_offset_divisibility hk r hkpow hsize
  have hm : k*((2^s)^(k-1)/k)=(2^s)^(k-1) := Nat.mul_div_cancel' hdiv
  have hk1 : 1≤k := by omega
  have hn : 0<k*2^s := Nat.mul_pos (by omega) (pow_pos (by decide) s)
  have hb : (k*2^s)*((2^s)^(k-1)/k)=(2^s)^k := by
    calc
      _ = 2^s*(k*((2^s)^(k-1)/k)) := by ring
      _ = 2^s*(2^s)^(k-1) := by rw [hm]
      _ = (2^s)^k := by
        simpa only [Nat.sub_add_cancel hk1] using (pow_succ' (2^s) (k-1)).symm
  refine ⟨hb,?_,Nat.div_le_self _ _⟩
  rw [←hb]
  simp [hn.ne']

end
end EntropyDesigns.SupportFace
