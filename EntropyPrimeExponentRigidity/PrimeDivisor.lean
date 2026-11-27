/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace EntropyDesigns.PrimeExponentRigidity

theorem prime_divisor_of_three_prime_power_successor (k l : ℕ)
    (hk : k.Prime) (hko : Odd k) (hl : l.Prime) (hl2 : l≠2)
    (hd : l∣3^k+1) : 2*k∣l-1 := by
  letI : Fact l.Prime := ⟨hl⟩
  have hl3 : 3≤l := by have h := hl.two_le;omega
  have hneg : (-1:ZMod l)≠1 := by
    intro he
    have hz2 : (2:ZMod l)=0 := by linear_combination -he
    have hdiv2 := (ZMod.natCast_eq_zero_iff 2 l).mp hz2
    have hle := Nat.le_of_dvd (by decide : 0<2) hdiv2
    omega
  have hz := (ZMod.natCast_eq_zero_iff (3^k+1) l).mpr hd
  have he : (3:ZMod l)^k= -1 := by
    push_cast at hz
    linear_combination hz
  have hthree : (3:ZMod l)≠0 := by
    intro h
    rw [h,zero_pow hk.ne_zero] at he
    norm_num at he
  have hnotk : (3:ZMod l)^k≠1 := by rw [he];exact hneg
  have hnottwo : (3:ZMod l)^2≠1 := by
    intro h
    have hz8 : (8:ZMod l)=0 := by linear_combination h
    have h8 := (ZMod.natCast_eq_zero_iff 8 l).mp hz8
    have h2 : l∣2 := hl.dvd_of_dvd_pow (show l∣2^3 by norm_num;exact h8)
    have hle := Nat.le_of_dvd (by decide : 0<2) h2
    omega
  let d := orderOf (3:ZMod l)
  have hpow : (3:ZMod l)^(2*k)=1 := by
    rw [Nat.mul_comm 2 k,pow_mul,he]
    norm_num
  have hdn : d∣2*k := orderOf_dvd_of_pow_eq_one hpow
  have h2d : 2∣d := by
    by_contra h
    have hc := (Nat.prime_two.coprime_iff_not_dvd.mpr h).symm
    have hdk : d∣k := hc.dvd_of_dvd_mul_left hdn
    exact hnotk (orderOf_dvd_iff_pow_eq_one.mp hdk)
  have hkd : k∣d := by
    by_contra h
    have hc := (hk.coprime_iff_not_dvd.mpr h).symm
    have hd2 : d∣2 := hc.dvd_of_dvd_mul_right hdn
    exact hnottwo (orderOf_dvd_iff_pow_eq_one.mp hd2)
  have hc : Nat.Coprime 2 k := hko.coprime_two_right.symm
  exact (hc.mul_dvd_of_dvd_of_dvd h2d hkd).trans (ZMod.orderOf_dvd_card_sub_one hthree)

end EntropyDesigns.PrimeExponentRigidity
