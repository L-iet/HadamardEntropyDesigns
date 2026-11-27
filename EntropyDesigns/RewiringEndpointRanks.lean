module

public import EntropyDesigns.RewiringRank

/-! # Exact initial and final ranks of the concrete rewiring -/

@[expose] public section
namespace EntropyDesigns

theorem rewireCode_initial_injective {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) :
    Function.Injective (maskPairCode (rewireMask e ∅)) := by
  intro u v hcode
  have hr : ∀ j, maskPairRow (rewireMask e ∅) u j = maskPairRow (rewireMask e ∅) v j := by
    intro j
    by_cases hj : j = Sum.inl ∅
    · subst j; simp [maskPairRow, rewireMask, walshChar]
    · simpa only [maskPairCode_sign] using congrArg (fun x => bitSign (x ⟨j, hj⟩)) hcode
  apply trapRow_injective e
  funext j
  have h := hr ((initialSwapIndex e).symm j)
  rw [rewireRow_initial_swap e he, rewireRow_initial_swap e he] at h
  simpa using h

theorem rewireLaw_initial_collision {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) :
    collision (rewireLaw e ∅) = 1 / (2 : ℝ) ^ (2 * s) := by
  classical
  have hi := pushLaw_injective_collision _ (rewireCode_initial_injective e he) (@trapSeedWeight s)
  have ht := pushLaw_injective_collision _ (trapCode_injective e) (@trapSeedWeight s)
  calc
    _ = collision (@trapSeedWeight s) := hi
    _ = collision (trapLaw e) := ht.symm
    _ = _ := trapLaw_collision e

noncomputable def rewiringRank {s : ℕ} (e : Finset (Fin s)) (k : ℕ) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear (rewireMask e (rewiringPrefix e k))))

theorem power_two_rank_unique (a b : ℕ) (h : 1 / (2 : ℝ) ^ a = 1 / (2 : ℝ) ^ b) : a = b := by
  have hp : (2 : ℝ) ^ a = (2 : ℝ) ^ b := by simpa only [one_div, inv_inj] using h
  have hn : (2 : ℕ) ^ a = 2 ^ b := by exact_mod_cast hp
  exact (Nat.pow_right_inj (by decide : 1 < (2 : ℕ))).mp hn

theorem rewiringRank_initial {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) :
    rewiringRank e 0 = 2 * s := by
  have h := rewireLaw_initial_collision e he
  change collision (maskPairLaw (rewireMask e ∅)) = _ at h
  rw [maskPairLaw_rank_collision] at h
  unfold rewiringRank
  rw [show rewiringPrefix e 0 = ∅ by simp [rewiringPrefix]]
  exact power_two_rank_unique _ _ h

theorem rewiringRank_final {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) :
    rewiringRank e (rewiringList e).length = s + 1 := by
  have h : collision (rewiringScheduleLaw e (rewiringList e).length) =
      1 / (2 * (2 : ℝ) ^ s) := by rw [rewiringSchedule_final e he, endpointLaw_collision]
  change collision (maskPairLaw (rewireMask e (rewiringPrefix e (rewiringList e).length))) = _ at h
  rw [maskPairLaw_rank_collision] at h
  have hpow : 1 / (2 : ℝ) ^ rewiringRank e (rewiringList e).length = 1 / (2 : ℝ) ^ (s + 1) := by
    rw [pow_succ, mul_comm ((2 : ℝ) ^ s) 2]
    exact h
  exact power_two_rank_unique _ _ hpow

theorem rewiringRank_step {s : ℕ} (e : Finset (Fin s)) (k : ℕ)
    (hk : k < (rewiringList e).length) :
    rewiringRank e k = rewiringRank e (k + 1) ∨ rewiringRank e k = rewiringRank e (k + 1) + 1 := by
  have hb := (rewiringList_members e (rewiringList e)[k]).mp (List.getElem_mem hk)
  unfold rewiringRank
  rw [rewiringPrefix_successor e k hk]
  exact rewire_rank_step e _ _ hb.1

end EntropyDesigns
