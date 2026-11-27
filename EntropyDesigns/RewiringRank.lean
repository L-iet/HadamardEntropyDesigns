module

public import EntropyDesigns.MaskLinearLaw
public import EntropyDesigns.RankOneRepair

/-! # Each actual mask replacement is a rank-one linear repair -/

@[expose] public section
namespace EntropyDesigns

def rightCoordinate {s : ℕ} (b : Finset (Fin s)) : TrapCoordinate s := ⟨Sum.inr b, by simp⟩

def leftCoordinate {s : ℕ} (b : Finset (Fin s)) (hb : b ≠ ∅) : TrapCoordinate s :=
  ⟨Sum.inl b, by simpa using hb⟩

def rewireDefect {s : ℕ} (b : Finset (Fin s)) (hb : b ≠ ∅) :
    (TrapCoordinate s → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj (R := ZMod 2) (φ := fun _ : TrapCoordinate s => ZMod 2) (rightCoordinate b) -
    LinearMap.proj (R := ZMod 2) (φ := fun _ : TrapCoordinate s => ZMod 2) (leftCoordinate b hb) -
    LinearMap.proj (R := ZMod 2) (φ := fun _ : TrapCoordinate s => ZMod 2) (rightCoordinate ∅)

def rewireRepair {s : ℕ} (b : Finset (Fin s)) (hb : b ≠ ∅) :
    (TrapCoordinate s → ZMod 2) →ₗ[ZMod 2] (TrapCoordinate s → ZMod 2) :=
  rankOneRepair (Pi.single (rightCoordinate b) 1) (rewireDefect b hb)

theorem rewireRepair_apply {s : ℕ} (b : Finset (Fin s)) (hb : b ≠ ∅)
    (x : TrapCoordinate s → ZMod 2) (j : TrapCoordinate s) :
    rewireRepair b hb x j = if j.val = Sum.inr b then
      x (leftCoordinate b hb) + x (rightCoordinate ∅) else x j := by
  classical
  change x j - rewireDefect b hb x *
    ((Pi.single (rightCoordinate b) (1 : ZMod 2) : TrapCoordinate s → ZMod 2) j) = _
  by_cases hj : j.val = Sum.inr b
  · have heq : j = rightCoordinate b := Subtype.ext hj
    subst j
    rw [ite_eq_left hj]
    simp [rewireDefect]
    ring
  · have hne : j ≠ rightCoordinate b := fun h => hj (congrArg Subtype.val h)
    simp [hj, hne]

theorem rewire_encoder_step {s : ℕ} (e b : Finset (Fin s)) (T : Finset (Finset (Fin s)))
    (hb : b ≠ ∅) : maskPairLinear (rewireMask e (insert b T)) =
      (rewireRepair b hb).comp (maskPairLinear (rewireMask e T)) := by
  apply LinearMap.ext
  intro u
  funext j
  rw [LinearMap.comp_apply]
  rw [rewireRepair_apply]
  by_cases hj : j.val = Sum.inr b
  · simp [hj, maskPairLinear, rewireMask, hb, leftCoordinate, rightCoordinate, maskFunctional]
  · rw [ite_eq_right hj]
    change maskFunctional (rewireMask e (insert b T) j.val).1 u.1 +
        maskFunctional (rewireMask e (insert b T) j.val).2 u.2 = _
    rw [rewireMask_insert e b T hb]
    simp only [Function.update_of_ne hj]
    rfl

theorem rewire_rank_step {s : ℕ} (e b : Finset (Fin s)) (T : Finset (Finset (Fin s))) (hb : b ≠ ∅) :
    Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear (rewireMask e T))) =
      Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear (rewireMask e (insert b T)))) ∨
    Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear (rewireMask e T))) =
      Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear (rewireMask e (insert b T)))) + 1 := by
  rw [rewire_encoder_step e b T hb]
  exact rankOneRepair_rank_dichotomy _ _ _

theorem rewireLaw_collision_nondecreasing {s : ℕ} (e b : Finset (Fin s))
    (T : Finset (Finset (Fin s))) (hb : b ≠ ∅) :
    collision (rewireLaw e T) ≤ collision (rewireLaw e (insert b T)) := by
  change collision (maskPairLaw (rewireMask e T)) ≤ collision (maskPairLaw (rewireMask e (insert b T)))
  rw [maskPairLaw_rank_collision, maskPairLaw_rank_collision]
  have h := rewire_rank_step e b T hb
  have hle : Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear (rewireMask e (insert b T)))) ≤
      Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear (rewireMask e T))) := by
    rcases h with h | h <;> omega
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hle)

theorem rewireLaw_step_dichotomy {s : ℕ} (e b : Finset (Fin s))
    (T : Finset (Finset (Fin s))) (hb : b ≠ ∅) :
    (collision (rewireLaw e (insert b T)) = collision (rewireLaw e T) ∧
      (Finset.univ.filter (fun x => rewireLaw e (insert b T) x ≠ 0)).card =
        (Finset.univ.filter (fun x => rewireLaw e T x ≠ 0)).card) ∨
    (collision (rewireLaw e (insert b T)) = 2 * collision (rewireLaw e T) ∧
      2 * (Finset.univ.filter (fun x => rewireLaw e (insert b T) x ≠ 0)).card =
        (Finset.univ.filter (fun x => rewireLaw e T x ≠ 0)).card) := by
  classical
  unfold rewireLaw
  simp only [maskPairLaw_rank_collision]
  rw [maskPairLaw_rank_support, maskPairLaw_rank_support]
  simpa only [linearLaw_collision, linearLaw_support_card] using
    linearLaw_single_rank_step (maskPairLinear (rewireMask e T))
      (maskPairLinear (rewireMask e (insert b T))) (rewire_rank_step e b T hb)

theorem rewiringSchedule_collision_nondecreasing {s : ℕ} (e : Finset (Fin s)) (k : ℕ)
    (hk : k < (rewiringList e).length) :
    collision (rewiringScheduleLaw e k) ≤ collision (rewiringScheduleLaw e (k + 1)) := by
  unfold rewiringScheduleLaw
  rw [rewiringPrefix_successor e k hk]
  have hb := (rewiringList_members e (rewiringList e)[k]).mp (List.getElem_mem hk)
  exact rewireLaw_collision_nondecreasing e _ _ hb.1

end EntropyDesigns
