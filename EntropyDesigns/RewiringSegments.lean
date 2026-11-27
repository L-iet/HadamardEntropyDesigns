module

public import EntropyDesigns.RewiringCounts
public import EntropyDesigns.RepairOverlap

/-! # Exact collision control on the actual replacement segments -/

@[expose] public section
namespace EntropyDesigns

noncomputable local instance {s : ℕ} : DecidableEq (TrapCoordinate s → ZMod 2) := Classical.decEq _

theorem rewireDefect_unit {s : ℕ} (b : Finset (Fin s)) (hb : b ≠ ∅) :
    rewireDefect b hb (Pi.single (rightCoordinate b) 1) = 1 := by
  classical
  have hleft : leftCoordinate b hb ≠ rightCoordinate b := by
    intro h; have hh := congrArg Subtype.val h; cases hh
  have hright : rightCoordinate (∅ : Finset (Fin s)) ≠ rightCoordinate b := by
    intro h
    have hh := congrArg Subtype.val h
    have : (∅ : Finset (Fin s)) = b := Sum.inr.inj hh
    exact hb this.symm
  simp [rewireDefect, hleft, hright]

theorem rewireDefect_witness {s : ℕ} (e b : Finset (Fin s)) (T : Finset (Finset (Fin s)))
    (hb : b ≠ ∅) (hbe : b ≠ e) (hbT : b ∉ T) :
    ∃ u : (Fin s → ZMod 2) × (Fin s → ZMod 2),
      rewireDefect b hb (maskPairLinear (rewireMask e T) u) = 1 := by
  obtain ⟨a, ha⟩ := maskFunctional_surjective b (Finset.nonempty_iff_ne_empty.mpr hb) 1
  refine ⟨(a, 0), ?_⟩
  simp [rewireDefect, maskPairLinear, rightCoordinate, leftCoordinate,
    rewireMask, hb, hbe, hbT, maskFunctional]
  change (∑ x ∈ b, a x) = 1 at ha
  exact ha

theorem maskPairLaw_bridge_linear {s : ℕ}
    (M N : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s)) (t : ℝ) :
    collision (probabilityBlend (maskPairLaw M) (maskPairLaw N) t) =
      collision (probabilityBlend (linearLaw (maskPairLinear M)) (linearLaw (maskPairLinear N)) t) := by
  classical
  rw [maskPairLaw_linear, maskPairLaw_linear, ← pushLaw_blend,
    pushLaw_injective_collision _ fieldCode_bijective.1]

theorem rewire_replacement_segment_bound {s : ℕ} (e b : Finset (Fin s)) (T : Finset (Finset (Fin s)))
    (hb : b ≠ ∅) (hbe : b ≠ e) (hbT : b ∉ T) (t : ℝ) :
    (3 / 4 : ℝ) * collision (rewireLaw e T) ≤
      collision (probabilityBlend (rewireLaw e T) (rewireLaw e (insert b T)) t) := by
  unfold rewireLaw
  rw [maskPairLaw_bridge_linear, maskPairLaw_rank_collision]
  have h := rankOneRepair_bridge_lower_bound (maskPairLinear (rewireMask e T))
    (Pi.single (rightCoordinate b) 1) (rewireDefect b hb) (rewireDefect_unit b hb)
    (rewireDefect_witness e b T hb hbe hbT) t
  rw [linearLaw_collision] at h
  rwa [rewire_encoder_step e b T hb]

theorem rewiringList_fresh {s : ℕ} (e : Finset (Fin s)) (k : ℕ)
    (hk : k < (rewiringList e).length) : (rewiringList e)[k] ∉ rewiringPrefix e k := by
  classical
  intro hmem
  have hm : (rewiringList e)[k] ∈ (rewiringList e).take k := by simpa [rewiringPrefix] using hmem
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hm
  have hi' : i < (rewiringList e).length := by simp only [List.length_take] at hi; omega
  have hik : i < k := by simp only [List.length_take] at hi; omega
  simp only [List.getElem_take] at heq
  have hidx := (rewiringList_nodup e).getElem_inj.mp heq
  omega

theorem rewiringSchedule_segment_bound {s : ℕ} (e : Finset (Fin s)) (k : ℕ)
    (hk : k < (rewiringList e).length) (t : ℝ) :
    (3 / 4 : ℝ) * collision (rewiringScheduleLaw e k) ≤
      collision (probabilityBlend (rewiringScheduleLaw e k) (rewiringScheduleLaw e (k + 1)) t) := by
  unfold rewiringScheduleLaw
  rw [rewiringPrefix_successor e k hk]
  have hb := (rewiringList_members e (rewiringList e)[k]).mp (List.getElem_mem hk)
  exact rewire_replacement_segment_bound e _ _ hb.1 hb.2 (rewiringList_fresh e k hk) t

end EntropyDesigns
