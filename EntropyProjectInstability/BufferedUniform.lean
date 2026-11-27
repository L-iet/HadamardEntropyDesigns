/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyGapTransfer.UniformTransfer
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
@[expose] public section
namespace EntropyDesigns.ProjectInstability
noncomputable section
open RelativeSequence GapTransfer

theorem binary_power_sub_one_odd {d : ℕ} (hd : 0<d) : Odd (2^d-1) := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have hp : 0<(2:ℕ)^a := pow_pos (by decide) _
  refine ⟨2^a-1,?_⟩
  rw [pow_succ]
  omega

/-- The explicit dyadic buffer converts a uniform exponent input into an
actual known order below h and the complete finite probability law.
This is only the arithmetic construction lemma; no asymptotic hypothesis
is hidden in its conclusions. -/
theorem buffered_uniform_exponent_law (s S : ℕ) (hS : S<s)
    (hbudget : s≤2^S) (hsmall : 2^S<2^s/2)
    (huniform : ∀ q : ℕ,Odd q → q≤2^s → knownHadamardOrder (2^S*q)) :
    knownHadamardOrder (2^s-2^S) ∧
    Nonempty (CompleteLawData (2^s-2^S) s) ∧
    2^s-(2^s-2^S)=2^S := by
  have hSle : S≤s := hS.le
  have hexp : 2^s=2^S*2^(s-S) := by
    rw [←pow_add]
    congr 1
    omega
  have hpow : 2^S≤(2:ℕ)^s := Nat.pow_le_pow_right (by decide) hSle
  have hqodd : Odd (2^(s-S)-1) := binary_power_sub_one_odd (by omega)
  have hqle : 2^(s-S)-1≤(2:ℕ)^s := by
    exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le s S))
  have hident : 2^S*(2^(s-S)-1)=2^s-2^S := by
    rw [Nat.mul_sub_left_distrib,hexp,mul_one]
  have hk := huniform _ hqodd hqle
  rw [hident] at hk
  have hgap : 2^s-(2^s-2^S)=2^S := by omega
  obtain ⟨K,hK⟩ := hk
  refine ⟨⟨K,hK⟩,spanning_summary_input ?_ ?_ K hK,hgap⟩
  · simpa only [hgap] using hbudget
  · simpa only [hgap] using hsmall

end
end EntropyDesigns.ProjectInstability
