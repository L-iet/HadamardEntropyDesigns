/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyRelativeSequence.SelectedOrders
public import EntropyRelativeSequence.ParameterLimits
@[expose] public section
namespace EntropyDesigns.RelativeSequence
open Filter
open scoped Topology

theorem power_half_gap {k s : ℕ}
    (hlo : k < 2^s) (hhi : 2^s < 2*k) :
    s ≠ 0 ∧ 2^s-k < 2^s/2 := by
  cases s with
  | zero => simp only [pow_zero] at hlo hhi; omega
  | succ s =>
    refine ⟨Nat.succ_ne_zero s, ?_⟩
    rw [pow_succ] at hlo hhi ⊢
    omega

/-- The selected classical orders satisfy the exact distance and entropy
scale limits required by the probability-law construction. -/
theorem selected_order_limits :
    ∃ a s : ℕ → ℕ,
      (∀ i, i ≤ a i) ∧
      (∀ i, s i ≠ 0 ∧ s i ≤ 2^(s i)-12^(a i) ∧
        2^(s i)-12^(a i) < 2^(s i)/2) ∧
      (∀ i, ∃ H : Matrix (Fin (12^(a i))) (Fin (12^(a i))) ℤ,
        Matrix.IsHadamard H) ∧
      Tendsto (fun i => ((12^(a i) : ℕ) : ℝ) / ((2^(s i) : ℕ) : ℝ)) atTop (nhds 1) ∧
      Tendsto (fun i => 1-1/((12^(a i) : ℕ) : ℝ)) atTop (nhds 1) ∧
      Tendsto (fun i => Real.log (((2^(s i) : ℕ) : ℝ) / ((12^(a i) : ℕ) : ℝ)))
        atTop (nhds 0) := by
  obtain ⟨a,s,ha,hgap,hbounds,hH,hratio⟩ := selected_hadamard_orders
  have hk (i : ℕ) : 0 < 12^(a i) := pow_pos (by decide) _
  have hkh (i : ℕ) : 12^(a i) < 2^(s i) := (hbounds i).1
  refine ⟨a,s,ha,?_,hH,hratio,?_,?_⟩
  · intro i
    have h := power_half_gap (hbounds i).1 (hbounds i).2
    exact ⟨h.1,hgap i,h.2⟩
  · exact sharp_distance_tends_one (fun i => 12^(a i)) (fun i => 2^(s i)) hk hkh hratio
  · exact entropy_scale_tends_zero (fun i => 12^(a i)) (fun i => 2^(s i)) hratio

end EntropyDesigns.RelativeSequence
