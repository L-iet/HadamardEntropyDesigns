/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyRelativeSequence.LawSequences
@[expose] public section
namespace EntropyDesigns.RelativeSequence
noncomputable section
open SupportFace
open Filter
open scoped Topology

theorem order_at_least_two {k s : ℕ} (hs : s ≠ 0)
    (hsmall : 2^s-k < 2^s/2) : 2 ≤ k := by
  cases s with
  | zero => exact False.elim (hs rfl)
  | succ s =>
    rw [pow_succ] at hsmall
    have hp : 0 < (2:ℕ)^s := pow_pos (by decide) _
    omega

/-- Actual feasible strict local traps with attained global comparisons and
sharp mixture distances along an unconditional infinite known-order sequence.
This does not yet assert the vertex or all-order entropy clauses. -/
theorem unconditional_spanning_laws :
    ∃ a s : ℕ → ℕ,
      (∀ i, i ≤ a i) ∧
      (∀ i, ∃ e : Finset (Fin (s i)), ∃ i0 : Fin (12^(a i)),
        e.Nonempty ∧ FullSpanningWitness (12^(a i)) (s i) e i0) ∧
      Tendsto (fun i => ((12^(a i):ℕ):ℝ)/((2^(s i):ℕ):ℝ)) atTop (nhds 1) ∧
      Tendsto (fun i => 1-1/((12^(a i):ℕ):ℝ)) atTop (nhds 1) ∧
      Tendsto (fun i => Real.log (((2^(s i):ℕ):ℝ)/((12^(a i):ℕ):ℝ)))
        atTop (nhds 0) := by
  obtain ⟨a,s,ha,hgap,hK,hr,hd,he⟩ := selected_order_limits
  have hk (i : ℕ) : 2 ≤ 12^(a i) := order_at_least_two (hgap i).1 (hgap i).2.2
  have hl := relative_spanning_laws (fun i => 12^(a i)) s hk
    (fun i => (hgap i).2.1) (fun i => (hgap i).2.2) hK hr
  exact ⟨a,s,ha,hl.1,hr,hd,he⟩

end
end EntropyDesigns.RelativeSequence
