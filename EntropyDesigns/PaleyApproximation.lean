/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.Paley
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Abel
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns
open Set Filter
open scoped Topology

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem independent_two_nine (a b : ℤ) (h : (2 : ℚ)^a*9^b=1) : a=0 ∧ b=0 := by
  have h22 : padicValRat 2 (2 : ℚ)=1 := padicValRat.self (by decide)
  have h29 : padicValRat 2 (9 : ℚ)=0 := by
    exact (padicValRat.of_nat (p := 2) (n := 9)).trans (by norm_num [padicValNat.eq_zero_of_not_dvd (by decide : ¬2∣9)])
  have h32 : padicValRat 3 (2 : ℚ)=0 := by
    exact (padicValRat.of_nat (p := 3) (n := 2)).trans (by norm_num [padicValNat.eq_zero_of_not_dvd (by decide : ¬3∣2)])
  have h39 : padicValRat 3 (9 : ℚ)=2 :=
    (padicValRat.of_nat (p := 3) (n := 9)).trans
      (by norm_num [padicValNat,Nat.maxPowDvdDiv,Nat.maxPowDvdDiv.go])
  have h2 := congrArg (padicValRat 2) h
  have h3 := congrArg (padicValRat 3) h
  rw [padicValRat.mul (by positivity) (by positivity)] at h2 h3
  simp only [padicValRat.zpow,h22,h29,h32,h39,padicValRat.one,mul_one,mul_zero,add_zero,zero_add] at h2 h3
  exact ⟨h2,by omega⟩

theorem irrational_log_nine_div_log_two : Irrational (Real.log 9/Real.log 2) := by
  rw [irrational_iff_ne_rational]
  intro a b hb heq
  have hlog : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hcross := (div_eq_div_iff hlog.ne' hbR).mp heq
  have hlogs : Real.log ((9 : ℝ)^b)=Real.log ((2 : ℝ)^a) := by
    rw [Real.log_zpow,Real.log_zpow]
    nlinarith
  have hpowers : (9 : ℝ)^b=(2 : ℝ)^a :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hlogs
  have hpowersQ : (9 : ℚ)^b=(2 : ℚ)^a := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact hpowers
  have hrel : (2 : ℚ)^(-a)*9^b=1 := by
    rw [zpow_neg,hpowersQ,inv_mul_cancel₀ (by positivity)]
  exact hb (independent_two_nine (-a) b hrel).2

theorem irrational_nat_circle_dense (a : ℝ) (ha : Irrational a) :
    DenseRange (fun n : ℕ => n • (a : AddCircle (1 : ℝ))) := by
  letI : Fact (0<(1 : ℝ)) := ⟨by norm_num⟩
  have hz : DenseRange (fun z : ℤ => z • (a : AddCircle (1 : ℝ))) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa only [div_one] using ha)
  exact denseRange_zsmul_iff_nsmul.mp hz

theorem irrational_shifted_tail_dense (a b : ℝ) (ha : Irrational a) (T : ℕ) :
    DenseRange (fun n : ℕ => (T+n) • (a : AddCircle (1 : ℝ))+(b : AddCircle (1 : ℝ))) := by
  let c : AddCircle (1 : ℝ) := T • (a : AddCircle (1 : ℝ))+(b : AddCircle (1 : ℝ))
  have hg : DenseRange (fun x : AddCircle (1 : ℝ) => x+c) := (Equiv.addRight c).surjective.denseRange
  have hh := hg.comp (irrational_nat_circle_dense a ha) (continuous_id.add continuous_const)
  have he : (fun n : ℕ => (T+n) • (a : AddCircle (1 : ℝ))+(b : AddCircle (1 : ℝ)))=
      (fun n : ℕ => n • (a : AddCircle (1 : ℝ))+c) := by
    funext n
    simp only [c,add_nsmul]
    abel
  rw [he]
  exact hh

theorem irrational_rotation_before_one (a b : ℝ) (ha : Irrational a) (T : ℕ)
    (ε : ℝ) (hε : 0<ε) :
    ∃ (n : ℕ) (m : ℤ) (x : ℝ),T≤n ∧ 1-ε<x ∧ x<1 ∧
      (n : ℝ)*a+b=(m : ℝ)+x := by
  let U : Set (AddCircle (1 : ℝ)) :=
    (fun x : ℝ => (x : AddCircle (1 : ℝ))) '' Set.Ioo (1-ε) 1
  have ho : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hne : U.Nonempty := ⟨((1-ε/2 : ℝ) : AddCircle (1 : ℝ)),
    ⟨1-ε/2,⟨by linarith,by linarith⟩,rfl⟩⟩
  obtain ⟨k,hk⟩ := (irrational_shifted_tail_dense a b ha T).exists_mem_open ho hne
  obtain ⟨x,⟨hxlo,hxhi⟩,hxeq⟩ := hk
  have hcoe : ((((T+k : ℕ) : ℝ)*a+b : ℝ) : AddCircle (1 : ℝ))=(x : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_add,show (((T+k : ℕ) : ℝ)*a)=(T+k) • a by rw [nsmul_eq_mul],AddCircle.coe_nsmul]
    exact hxeq.symm
  have hz : (((((T+k : ℕ) : ℝ)*a+b)-x : ℝ) : AddCircle (1 : ℝ))=0 := by
    rw [AddCircle.coe_sub,hcoe,sub_self]
  obtain ⟨m,hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  have hm' : (m : ℝ)=(((T+k : ℕ) : ℝ)*a+b)-x := by simpa only [zsmul_eq_mul,mul_one] using hm
  exact ⟨T+k,m,x,by omega,hxlo,hxhi,by linarith⟩

theorem paley_power_ratio_approximation (δ : ℝ) (hδ : 0 < δ) (T : ℕ) :
    ∃ n r : ℕ, T ≤ n ∧ 1 ≤ n ∧
      (3 : ℝ)^(2*n+1) < 2^r ∧
      1-δ < (3 : ℝ)^(2*n+1)/2^r := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have h9 : Real.log (9 : ℝ) = 2*Real.log 3 := by
    rw [show (9 : ℝ)=3^2 by norm_num,Real.log_pow]
    norm_num
  have h32 : Real.log (2 : ℝ) < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hα : 1 < Real.log (9 : ℝ)/Real.log 2 := by
    apply (lt_div_iff₀ h2).mpr
    rw [h9]
    linarith
  let ε := min δ (1/2 : ℝ)
  have hε : 0 < ε := lt_min hδ (by norm_num)
  obtain ⟨n,m,x,hn,hxlo,hxhi,heq⟩ := irrational_rotation_before_one
    (Real.log 9/Real.log 2) (Real.log 3/Real.log 2)
    irrational_log_nine_div_log_two (max T 1) ε hε
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hβ : 0 < Real.log (3 : ℝ)/Real.log 2 := div_pos h3 h2
  have hmpos : (0 : ℝ) < m := by nlinarith
  have hm : 0 ≤ m := by exact_mod_cast hmpos.le
  let r := m.toNat+1
  have hr : (r : ℝ)=(m : ℝ)+1 := by
    have hh : (m.toNat : ℤ)=m := Int.toNat_of_nonneg hm
    have hhR : (m.toNat : ℝ)=(m : ℝ) := by exact_mod_cast hh
    simp only [r,Nat.cast_add,Nat.cast_one,hhR]
  have hcross : (n : ℝ)*Real.log 9+Real.log 3=((m : ℝ)+x)*Real.log 2 := by
    have he := congrArg (fun y : ℝ => y*Real.log 2) heq
    field_simp at he
    nlinarith
  have hlog : Real.log ((3 : ℝ)^(2*n+1)/2^r)=(x-1)*Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity),Real.log_pow,Real.log_pow]
    push_cast
    rw [h9] at hcross
    nlinarith
  have hratio : (3 : ℝ)^(2*n+1)/2^r=Real.exp ((x-1)*Real.log 2) := by
    rw [← hlog,Real.exp_log (by positivity)]
  have hupper : (3 : ℝ)^(2*n+1)/2^r < 1 := by
    rw [hratio]
    apply (Real.exp_lt_one_iff).mpr
    exact mul_neg_of_neg_of_pos (by linarith) h2
  have hlogle : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith
  have hεle : ε ≤ δ := min_le_left _ _
  have hlower : 1-δ < (3 : ℝ)^(2*n+1)/2^r := by
    rw [hratio]
    have hexp := Real.add_one_le_exp ((x-1)*Real.log 2)
    have hxl : -δ < x-1 := by linarith
    have hxneg : x-1 < 0 := by linarith
    have hmul : x-1 ≤ (x-1)*Real.log 2 := by nlinarith
    linarith
  exact ⟨n,r,le_trans (le_max_left _ _) hn,hn1,
    (div_lt_one (by positivity)).mp hupper,hlower⟩


theorem paley_near_binary_orders (δ : ℝ) (hδ : 0 < δ) (T : ℕ) :
    ∃ n r : ℕ, T ≤ n ∧ 1 ≤ n ∧ 3 ≤ r ∧
      28 ≤ 3^(2*n+1)+1 ∧
      3^(2*n+1)+1+4 ≤ 2^r ∧
      2^r ≤ 2*(3^(2*n+1)+1-4) ∧
      1-δ < ((3^(2*n+1)+1 : ℕ) : ℝ)/(2^r : ℕ) := by
  obtain ⟨n,r,hn,hn1,hqlt,hclose⟩ := paley_power_ratio_approximation
    (min δ (1/4)) (lt_min hδ (by norm_num)) T
  let q : ℕ := 3^(2*n+1)
  let L : ℕ := 2^r
  have hq27 : 27 ≤ q := by
    exact Nat.pow_le_pow_right (by decide : 0<3) (by omega : 3≤2*n+1)
  have hqL : q < L := by exact_mod_cast hqlt
  have hL28 : 28 ≤ L := by omega
  have hr : 3 ≤ r := by
    by_contra hh
    have hsmall : L ≤ 4 := Nat.pow_le_pow_right (by decide : 0<2) (by omega : r≤2)
    omega
  have hL8 : 8 ∣ L := by
    obtain ⟨s,hs⟩ := Nat.exists_eq_add_of_le hr
    refine ⟨2^s,?_⟩
    simp only [L,hs,pow_add]
    norm_num
  have hres := paley_three_power_order_residue n
  change (q+1)%8=4 at hres
  have hgap : q+1+4 ≤ L := by
    have hLm := Nat.mod_eq_zero_of_dvd hL8
    omega
  have hLp : (0 : ℝ)<L := by exact_mod_cast (by omega : 0<L)
  have hclose' : 1-min δ (1/4) < (q : ℝ)/L := by exact_mod_cast hclose
  have hthree : (3/4 : ℝ)<(q : ℝ)/L := by
    have := min_le_right δ (1/4 : ℝ)
    linarith
  have hthree' := (lt_div_iff₀ hLp).mp hthree
  have hqR : (27 : ℝ)≤q := by exact_mod_cast hq27
  have hLR : (28 : ℝ)≤L := by exact_mod_cast hL28
  have hhalfR : (L : ℝ) ≤ 2*((q : ℝ)-3) := by nlinarith
  have hq3 : 3≤q := by omega
  have hhalf : L ≤ 2*(q+1-4) := by
    have hcast : ((q+1-4 : ℕ) : ℝ)=(q : ℝ)-3 := by
      rw [Nat.cast_sub (by omega : 4≤q+1)]
      push_cast
      ring
    rw [← hcast] at hhalfR
    exact_mod_cast hhalfR
  have hratio : 1-δ < ((q+1 : ℕ) : ℝ)/L := by
    have hm := min_le_left δ (1/4 : ℝ)
    have hle : (q : ℝ)/L ≤ ((q+1 : ℕ) : ℝ)/L := by
      apply div_le_div_of_nonneg_right _ hLp.le
      norm_cast
      omega
    linarith
  exact ⟨n,r,hn,hn1,hr,by omega,hgap,hhalf,hratio⟩

end EntropyDesigns
