module

public import EntropyDesigns.RewiringSegments
public import EntropyDesigns.InitialSwapOverlap

/-! # The actual feasible piecewise-affine rewiring path and its exact minimum -/

@[expose] public section
namespace EntropyDesigns

noncomputable def rewiringPath {s : ℕ} (e : Finset (Fin s))
    (j : Fin ((rewiringList e).length + 1)) (t : ℝ) : (TrapCoordinate s → Bool) → ℝ :=
  Fin.cases (probabilityBlend (trapLaw e) (rewireLaw e ∅) t)
    (fun k => probabilityBlend (rewiringScheduleLaw e k.val) (rewiringScheduleLaw e (k.val + 1)) t) j

theorem observedFeasible_blend {s : ℕ} (p q : (TrapCoordinate s → Bool) → ℝ)
    (hp : observedFeasible p) (hq : observedFeasible q) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    observedFeasible (probabilityBlend p q t) := by
  classical
  refine ⟨probabilityBlend_nonneg p q t hp.1 hq.1 ht ht',
    probabilityBlend_mass p q t hp.2.1 hq.2.1, ?_, ?_⟩
  · intro j
    exact probabilityBlend_moment p q (fun x => (bitSign (x j) : ℝ)) t 0
      (hp.2.2.1 j) (hq.2.2.1 j)
  · intro i j hij
    have hpi : (∑ x, p x * ((bitSign (x i) : ℝ) * (bitSign (x j) : ℝ))) = 0 := by
      simpa only [mul_assoc] using hp.2.2.2 i j hij
    have hqi : (∑ x, q x * ((bitSign (x i) : ℝ) * (bitSign (x j) : ℝ))) = 0 := by
      simpa only [mul_assoc] using hq.2.2.2 i j hij
    simpa only [mul_assoc] using probabilityBlend_moment p q
      (fun x => (bitSign (x i) : ℝ) * (bitSign (x j) : ℝ)) t 0 hpi hqi

theorem rewiringPath_feasible {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (j : Fin ((rewiringList e).length + 1)) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    observedFeasible (rewiringPath e j t) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · exact observedFeasible_blend _ _
      ⟨(trapLaw_probability e).1, (trapLaw_probability e).2, trapLaw_mean e he, trapLaw_pair e he⟩
      (rewireLaw_feasible e he ∅) t ht ht'
  · exact observedFeasible_blend _ _ (rewiringSchedule_feasible e he k.val)
      (rewiringSchedule_feasible e he (k.val + 1)) t ht ht'

theorem rewiringSchedule_collision_lower {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (k : ℕ) (hk : k ≤ (rewiringList e).length) :
    1 / (2 : ℝ) ^ (2 * s) ≤ collision (rewiringScheduleLaw e k) := by
  have haux : ∀ n : ℕ, n ≤ (rewiringList e).length →
      1 / (2 : ℝ) ^ (2 * s) ≤ collision (rewiringScheduleLaw e n) := by
    intro n
    induction n with
    | zero => intro hn; rw [rewiringSchedule_initial, rewireLaw_initial_collision e he]
    | succ n ih =>
      intro hn
      exact le_trans (ih (by omega)) (rewiringSchedule_collision_nondecreasing e n (by omega))
  exact haux k hk

theorem rewiringPath_collision_lower {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty)
    (j : Fin ((rewiringList e).length + 1)) (t : ℝ) :
    3 / (4 * (2 : ℝ) ^ (2 * s)) ≤ collision (rewiringPath e j t) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · exact (initial_swap_bridge_minimum hs e he).2 t
  · have hbase := rewiringSchedule_collision_lower e he k.val (Nat.le_of_lt k.isLt)
    have hseg := rewiringSchedule_segment_bound e k.val k.isLt t
    calc
      _ = (3 / 4 : ℝ) * (1 / (2 : ℝ) ^ (2 * s)) := by ring
      _ ≤ (3 / 4 : ℝ) * collision (rewiringScheduleLaw e k.val) := by gcongr
      _ ≤ _ := hseg

theorem rewiringPath_minimum_attained {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) :
    collision (rewiringPath e 0 (1 / 2)) = 3 / (4 * (2 : ℝ) ^ (2 * s)) :=
  (initial_swap_bridge_minimum hs e he).1

theorem rewiringPath_start {s : ℕ} (e : Finset (Fin s)) : rewiringPath e 0 0 = trapLaw e := by
  funext x
  simp [rewiringPath, probabilityBlend]

theorem rewiringPath_swap_end {s : ℕ} (e : Finset (Fin s)) : rewiringPath e 0 1 = rewireLaw e ∅ := by
  funext x
  simp [rewiringPath, probabilityBlend]

theorem rewiringPath_succ_start {s : ℕ} (e : Finset (Fin s)) (k : Fin (rewiringList e).length) :
    rewiringPath e k.succ 0 = rewiringScheduleLaw e k.val := by
  funext x
  simp [rewiringPath, probabilityBlend]

theorem rewiringPath_succ_end {s : ℕ} (e : Finset (Fin s)) (k : Fin (rewiringList e).length) :
    rewiringPath e k.succ 1 = rewiringScheduleLaw e (k.val + 1) := by
  funext x
  simp [rewiringPath, probabilityBlend]

theorem rewiringPath_join {s : ℕ} (e : Finset (Fin s)) (k : Fin (rewiringList e).length) :
    rewiringPath e k.castSucc 1 = rewiringPath e k.succ 0 := by
  rw [rewiringPath_succ_start]
  by_cases hk : k.val = 0
  · have hk0 : k.castSucc = (0 : Fin ((rewiringList e).length + 1)) := Fin.ext hk
    rw [hk0, rewiringPath_swap_end, hk, rewiringSchedule_initial]
  · let p : Fin (rewiringList e).length := ⟨k.val - 1, by omega⟩
    have heq : k.castSucc = p.succ := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_succ]
      dsimp [p]
      omega
    rw [heq, rewiringPath_succ_end]
    congr 1
    dsimp [p]
    omega

theorem rewiringPath_finish {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) :
    rewiringPath e (Fin.last (rewiringList e).length) 1 = endpointLaw s := by
  have hpow : (4 : ℕ) ≤ 2 ^ s := by exact_mod_cast two_pow_ge_four hs
  have hlen := rewiringList_length e he
  have hn : 0 < (rewiringList e).length := by omega
  let p : Fin (rewiringList e).length := ⟨(rewiringList e).length - 1, by omega⟩
  have heq : Fin.last (rewiringList e).length = p.succ := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.val_succ]
    dsimp [p]
    omega
  rw [heq, rewiringPath_succ_end]
  have hp : p.val + 1 = (rewiringList e).length := by dsimp [p]; omega
  rw [hp, rewiringSchedule_final e he]

theorem rewiringPath_minimum {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) :
    (∀ j : Fin ((rewiringList e).length + 1), ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      observedFeasible (rewiringPath e j t) ∧
        3 / (4 * (2 : ℝ) ^ (2 * s)) ≤ collision (rewiringPath e j t)) ∧
    collision (rewiringPath e 0 (1 / 2)) = 3 / (4 * (2 : ℝ) ^ (2 * s)) := by
  refine ⟨?_, rewiringPath_minimum_attained hs e he⟩
  intro j t ht ht'
  exact ⟨rewiringPath_feasible e he j t ht ht', rewiringPath_collision_lower hs e he j t⟩

theorem rewiringPath_affine {s : ℕ} (e : Finset (Fin s))
    (j : Fin ((rewiringList e).length + 1)) (t : ℝ) (x : TrapCoordinate s → Bool) :
    rewiringPath e j t x = (1 - t) * rewiringPath e j 0 x + t * rewiringPath e j 1 x := by
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [rewiringPath, probabilityBlend]

end EntropyDesigns
