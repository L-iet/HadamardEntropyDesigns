module

public import EntropyDesigns.RewiringEndpointRanks

/-! # Exact number of rank drops and support-preserving jumps -/

@[expose] public section
namespace EntropyDesigns

def rankDropSteps (r : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun k => r k = r (k + 1) + 1)

theorem rank_walk_drop_count (r : ℕ → ℕ) (n : ℕ)
    (hstep : ∀ k < n, r k = r (k + 1) ∨ r k = r (k + 1) + 1) :
    ((rankDropSteps r n).card : ℤ) = (r 0 : ℤ) - r n := by
  have hp : ∀ k ∈ Finset.range n,
      (if r k = r (k + 1) + 1 then (1 : ℤ) else 0) = (r k : ℤ) - r (k + 1) := by
    intro k hk
    have h := hstep k (Finset.mem_range.mp hk)
    split_ifs <;> omega
  have ht : ∀ m : ℕ, (∑ k ∈ Finset.range m, ((r k : ℤ) - r (k + 1))) = (r 0 : ℤ) - r m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  calc
    _ = ∑ k ∈ Finset.range n, if r k = r (k + 1) + 1 then (1 : ℤ) else 0 := by
      simp [rankDropSteps]
    _ = _ := by rw [Finset.sum_congr rfl hp, ht]

theorem rewiring_rank_drop_count {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) :
    (rankDropSteps (rewiringRank e) (rewiringList e).length).card = s - 1 := by
  have h := rank_walk_drop_count (rewiringRank e) (rewiringList e).length (rewiringRank_step e)
  rw [rewiringRank_initial e he, rewiringRank_final e he] at h
  push_cast at h
  omega

theorem rewiring_preserving_jump_count {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) :
    ((Finset.range (rewiringList e).length).filter
      (fun k => rewiringRank e k = rewiringRank e (k + 1))).card + 1 = 2 ^ s - s := by
  have hp := Finset.card_filter_add_card_filter_not (s := Finset.range (rewiringList e).length)
    (fun k => rewiringRank e k = rewiringRank e (k + 1) + 1)
  have hfilter : (Finset.range (rewiringList e).length).filter
      (fun k => ¬rewiringRank e k = rewiringRank e (k + 1) + 1) =
      (Finset.range (rewiringList e).length).filter
        (fun k => rewiringRank e k = rewiringRank e (k + 1)) := by
    apply Finset.filter_congr
    intro k hk
    have h := rewiringRank_step e k (Finset.mem_range.mp hk)
    omega
  rw [hfilter, ← rankDropSteps, rewiring_rank_drop_count hs e he, Finset.card_range,
    rewiringList_length e he] at hp
  have hpow : (4 : ℕ) ≤ 2 ^ s := by exact_mod_cast two_pow_ge_four hs
  rw [rewiringList_length e he]
  omega

theorem rewiringSchedule_rank_collision {s : ℕ} (e : Finset (Fin s)) (k : ℕ) :
    collision (rewiringScheduleLaw e k) = 1 / (2 : ℝ) ^ rewiringRank e k := by
  unfold rewiringScheduleLaw rewireLaw rewiringRank
  exact maskPairLaw_rank_collision _

theorem rewiringSchedule_rank_support {s : ℕ} (e : Finset (Fin s)) (k : ℕ) :
    (Finset.univ.filter (fun x => rewiringScheduleLaw e k x ≠ 0)).card = 2 ^ rewiringRank e k := by
  classical
  unfold rewiringScheduleLaw rewireLaw rewiringRank
  exact maskPairLaw_rank_support _

theorem rewiring_halving_step_iff {s : ℕ} (e : Finset (Fin s)) (k : ℕ) :
    (2 * (Finset.univ.filter (fun x => rewiringScheduleLaw e (k + 1) x ≠ 0)).card =
        (Finset.univ.filter (fun x => rewiringScheduleLaw e k x ≠ 0)).card ∧
      collision (rewiringScheduleLaw e (k + 1)) = 2 * collision (rewiringScheduleLaw e k)) ↔
    rewiringRank e k = rewiringRank e (k + 1) + 1 := by
  classical
  rw [rewiringSchedule_rank_support, rewiringSchedule_rank_support,
    rewiringSchedule_rank_collision, rewiringSchedule_rank_collision]
  have hp : (2 : ℕ) * 2 ^ rewiringRank e (k + 1) = 2 ^ (rewiringRank e (k + 1) + 1) := by
    rw [pow_succ, Nat.mul_comm]
  rw [hp, Nat.pow_right_inj (by decide : 1 < (2 : ℕ))]
  constructor
  · intro h; exact h.1.symm
  · intro h
    refine ⟨h.symm, ?_⟩
    rw [h, pow_succ]
    field_simp

theorem rewiring_preserving_step_iff {s : ℕ} (e : Finset (Fin s)) (k : ℕ) :
    ((Finset.univ.filter (fun x => rewiringScheduleLaw e (k + 1) x ≠ 0)).card =
        (Finset.univ.filter (fun x => rewiringScheduleLaw e k x ≠ 0)).card ∧
      collision (rewiringScheduleLaw e (k + 1)) = collision (rewiringScheduleLaw e k)) ↔
    rewiringRank e k = rewiringRank e (k + 1) := by
  classical
  rw [rewiringSchedule_rank_support, rewiringSchedule_rank_support,
    rewiringSchedule_rank_collision, rewiringSchedule_rank_collision,
    Nat.pow_right_inj (by decide : 1 < (2 : ℕ))]
  constructor
  · intro h; exact h.1.symm
  · intro h; simp [h]

theorem rewiring_support_halving_jump_count {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) :
    ((Finset.range (rewiringList e).length).filter (fun k =>
      2 * (Finset.univ.filter (fun x => rewiringScheduleLaw e (k + 1) x ≠ 0)).card =
          (Finset.univ.filter (fun x => rewiringScheduleLaw e k x ≠ 0)).card ∧
        collision (rewiringScheduleLaw e (k + 1)) = 2 * collision (rewiringScheduleLaw e k))).card = s - 1 := by
  classical
  simp only [rewiring_halving_step_iff]
  exact rewiring_rank_drop_count hs e he

theorem rewiring_support_preserving_jump_count {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) :
    ((Finset.range (rewiringList e).length).filter (fun k =>
      (Finset.univ.filter (fun x => rewiringScheduleLaw e (k + 1) x ≠ 0)).card =
          (Finset.univ.filter (fun x => rewiringScheduleLaw e k x ≠ 0)).card ∧
        collision (rewiringScheduleLaw e (k + 1)) = collision (rewiringScheduleLaw e k))).card + 1 = 2 ^ s - s := by
  classical
  simp only [rewiring_preserving_step_iff]
  exact rewiring_preserving_jump_count hs e he

theorem initial_swap_preserves_support_collision {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) :
    collision (rewiringScheduleLaw e 0) = collision (trapLaw e) ∧
    (Finset.univ.filter (fun x => rewiringScheduleLaw e 0 x ≠ 0)).card =
      (Finset.univ.filter (fun x => trapLaw e x ≠ 0)).card := by
  classical
  constructor
  · rw [rewiringSchedule_initial, rewireLaw_initial_collision e he, trapLaw_collision]
  · rw [rewiringSchedule_rank_support, rewiringRank_initial e he, trapLaw_support_card]

end EntropyDesigns
