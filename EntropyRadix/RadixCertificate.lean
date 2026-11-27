/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyRadix.RadixLogBounds
public import HadamardMultibase.CraigenTransfer
public import HadamardMultibase.Turyn
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Base
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns
open HadamardMultibase

theorem list_sum_scaled (l : List ℕ) (B : ℕ) :
    (l.map (fun n => B*n)).sum=B*l.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih,Nat.mul_add]

theorem golay_radix_representation (k w : ℕ) (hk : 0<k)
    (hcert : ∀ a : ℕ,a<2^k → ∃ l : List ℕ,
      (∀ n∈l,GolayLength n) ∧ l.sum=a ∧ l.length≤w) :
    ∀ d q : ℕ,q<(2^k)^d → ∃ l : List ℕ,
      (∀ n∈l,GolayLength n) ∧ l.sum=q ∧ l.length≤w*d := by
  intro d
  induction d with
  | zero =>
    intro q hq
    have hq0 : q=0 := by simpa using hq
    subst q
    exact ⟨[],by simp,by simp,by simp⟩
  | succ d ih =>
    intro q hq
    have hB := radix_base_gt_one hk
    have hquot : q/(2^k)<(2^k)^d := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0<2^k)).mpr
      simpa [pow_succ,Nat.mul_comm] using hq
    obtain ⟨upper,hupper,hsum,hlen⟩ := ih (q/(2^k)) hquot
    obtain ⟨digit,hdigit,hdsum,hdlen⟩ := hcert (q%(2^k)) (Nat.mod_lt _ (by omega))
    refine ⟨digit++upper.map (fun n => 2^k*n),?_,?_,?_⟩
    · intro n hn
      rcases List.mem_append.mp hn with hn|hn
      · exact hdigit n hn
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hn
        exact (golayLength_two.pow k).mul (hupper a ha)
    · rw [List.sum_append,list_sum_scaled,hdsum,hsum]
      exact Nat.mod_add_div q (2^k)
    · simp only [List.length_append,List.length_map]
      nlinarith

theorem finite_radix_exponent_bound (k w : ℕ) (hk : 0<k)
    (hcert : ∀ a : ℕ,a<2^k → ∃ l : List ℕ,
      (∀ n∈l,GolayLength n) ∧ l.sum=a ∧ l.length≤w) (q : ℕ) :
    ∃ t : ℕ,HadamardOrder (2^t*(2*q+1)) ∧
      t≤2*w*Nat.clog (2^k) (q+1)+2 := by
  have hbase := radix_base_gt_one hk
  have hq : q<(2^k)^Nat.clog (2^k) (q+1) := by
    have hh := Nat.le_pow_clog hbase (q+1)
    omega
  obtain ⟨l,hgolay,hsum,hlen⟩ := golay_radix_representation k w hk hcert _ q hq
  have hh := craigenTransfer l hgolay
  rw [four_pow_eq_two_pow,hsum] at hh
  exact ⟨2*l.length+2,hh,by nlinarith⟩

theorem finite_radix_hadamard_bound (k w : ℕ) (hk : 0<k)
    (hcert : ∀ a : ℕ,a<2^k → ∃ l : List ℕ,
      (∀ n∈l,GolayLength n) ∧ l.sum=a ∧ l.length≤w)
    {p : ℕ} (hp : Odd p) (hp1 : 1<p) :
    ∃ t : ℕ,HadamardOrder (2^t*p) ∧
      t≤2*w*Nat.clog (2^k) ((p-1)/2+1)+2 ∧
      (t:ℝ)≤(2*(w:ℝ)/(k:ℝ))*(Real.log (p:ℝ)/Real.log 2)+2*(w:ℝ)+2 := by
  obtain ⟨q,rfl⟩ := hp.exists_bit1
  have hq : 0<q := by omega
  obtain ⟨t,hH,ht⟩ := finite_radix_exponent_bound k w hk hcert q
  have hlog := radix_finite_to_log_bound hk hq ht
  refine ⟨t,hH,?_,?_⟩
  · have he : (2*q+1-1)/2=q := by omega
    rw [he]
    exact ht
  · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hlog

end EntropyDesigns
