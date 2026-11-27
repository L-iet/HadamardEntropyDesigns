module

public import EntropyDesigns.RewiringLaws
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Lattice.Lemmas

/-! # A finite, explicit list of the one-column replacements -/

@[expose] public section
namespace EntropyDesigns

noncomputable def rewiringList {s : ℕ} (e : Finset (Fin s)) : List (Finset (Fin s)) :=
  ((Finset.univ.erase ∅).erase e).toList

noncomputable def rewiringPrefix {s : ℕ} (e : Finset (Fin s)) (k : ℕ) : Finset (Finset (Fin s)) :=
  ((rewiringList e).take k).toFinset

theorem rewiringList_nodup {s : ℕ} (e : Finset (Fin s)) : (rewiringList e).Nodup := by
  classical
  exact Finset.nodup_toList _

theorem rewiringList_members {s : ℕ} (e b : Finset (Fin s)) :
    b ∈ rewiringList e ↔ b ≠ ∅ ∧ b ≠ e := by
  classical
  simp [rewiringList, and_comm]

theorem rewiringList_length {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) :
    (rewiringList e).length = 2 ^ s - 2 := by
  classical
  have hmem : e ∈ (Finset.univ : Finset (Finset (Fin s))).erase ∅ := by simp [he.ne_empty]
  unfold rewiringList
  rw [Finset.length_toList, Finset.card_erase_of_mem hmem,
    Finset.card_erase_of_mem (Finset.mem_univ ∅)]
  simp [Nat.sub_sub]

theorem rewiring_total_jumps {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) :
    (rewiringList e).length + 1 = 2 ^ s - 1 := by
  rw [rewiringList_length e he]
  have h : (4 : ℕ) ≤ 2 ^ s := by exact_mod_cast two_pow_ge_four hs
  omega

theorem rewiringPrefix_successor {s : ℕ} (e : Finset (Fin s)) (k : ℕ)
    (hk : k < (rewiringList e).length) :
    rewiringPrefix e (k + 1) = insert (rewiringList e)[k] (rewiringPrefix e k) := by
  classical
  unfold rewiringPrefix
  rw [List.take_succ_eq_append_getElem hk]
  simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
    Finset.union_insert, Finset.union_empty]

theorem rewiringSchedule_mask_step {s : ℕ} (e : Finset (Fin s)) (k : ℕ)
    (hk : k < (rewiringList e).length) :
    rewireMask e (rewiringPrefix e (k + 1)) =
      Function.update (rewireMask e (rewiringPrefix e k)) (Sum.inr (rewiringList e)[k])
        ((rewiringList e)[k], e) := by
  have hb := (rewiringList_members e (rewiringList e)[k]).mp (List.getElem_mem hk)
  rw [rewiringPrefix_successor e k hk]
  exact rewireMask_insert e _ _ hb.1

theorem rewireMask_full_prefix {s : ℕ} (e : Finset (Fin s)) :
    rewireMask e (rewiringPrefix e (rewiringList e).length) = rewireMask e Finset.univ := by
  classical
  have hprefix : rewiringPrefix e (rewiringList e).length = (Finset.univ.erase ∅).erase e := by
    unfold rewiringPrefix
    rw [List.take_length]
    simp [rewiringList]
  rw [hprefix]
  funext j
  cases j with
  | inl S => rfl
  | inr S =>
    by_cases hS : S = ∅ <;> by_cases hSe : S = e <;>
      simp [rewireMask, hS, hSe]

noncomputable def rewiringScheduleLaw {s : ℕ} (e : Finset (Fin s)) (k : ℕ) :
    (TrapCoordinate s → Bool) → ℝ := rewireLaw e (rewiringPrefix e k)

theorem rewiringSchedule_feasible {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) (k : ℕ) :
    observedFeasible (rewiringScheduleLaw e k) := rewireLaw_feasible e he _

theorem rewiringSchedule_initial {s : ℕ} (e : Finset (Fin s)) :
    rewiringScheduleLaw e 0 = rewireLaw e ∅ := by
  simp [rewiringScheduleLaw, rewiringPrefix]

theorem rewiringSchedule_final {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) :
    rewiringScheduleLaw e (rewiringList e).length = endpointLaw s := by
  unfold rewiringScheduleLaw rewireLaw
  rw [rewireMask_full_prefix]
  exact rewireLaw_final e he

end EntropyDesigns
