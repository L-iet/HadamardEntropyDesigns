/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCompleteSequence.AllEntropy
public import EntropySpanningSlopes.SpanningExistence
@[expose] public section
namespace EntropyDesigns.RelativeSequence
noncomputable section
open SupportFace ConcentratedFamily SpanningSlopes
open scoped BigOperators

theorem source_all_entropy_lower {k s : ℕ} (i0 : Fin k)
    (w : SourceOutcome k s i0 → ℝ) (hw : sourceFeasible i0 w) :
    (∀ α : ℝ, 0 < α → Real.log ((k*2^s:ℕ):ℝ) ≤ renyiEntropy w α) ∧
    Real.log ((k*2^s:ℕ):ℝ) ≤ minEntropy w := by
  have hn : (0:ℝ) < ((k*2^s:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.zero_lt_of_lt i0.isLt) (pow_pos (by decide) s)
  exact ⟨fun α hα => renyi_all_lower w hw.1 hw.2.1 _ α hn hα (source_global_atom_cap i0 w hw),
    minEntropy_lower w hw.2.1 _ hn (source_global_atom_cap i0 w hw)⟩

theorem source_uniform_of_collision {k s : ℕ} (i0 : Fin k)
    (w : SourceOutcome k s i0 → ℝ) (hw : sourceFeasible i0 w)
    (hC : collision w = 1/((k*2^s:ℕ):ℝ)) :
    ∀ y, w y = 0 ∨ w y = 1/((k*2^s:ℕ):ℝ) := by
  classical
  have hh : collision w = 1/(Fintype.card (Option (SourceCoordinate k s i0)):ℝ) := by
    simpa only [augmented_coordinate_card i0] using hC
  have hu := finite_frame_equality_uniform (sourceFrame i0) w
    (sourceFrame_sign i0) hw.1 hw.2.1 (sourceFrame_isotropic i0 w hw) hh
  simpa only [augmented_coordinate_card i0] using hu

theorem source_all_entropy_optimizer {k s : ℕ} (i0 : Fin k)
    (e : Finset (Fin s)) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    ∃ q : SourceOutcome k s i0 → ℝ, sourceFeasible i0 q ∧
      (∀ α : ℝ, 0 < α → renyiEntropy q α = Real.log ((k*2^s:ℕ):ℝ)) ∧
      minEntropy q = Real.log ((k*2^s:ℕ):ℝ) := by
  obtain ⟨q,hq,hC,hmax⟩ := source_optimizer_of_known_hadamard i0 e K hK
  have hn : (0:ℝ) < ((k*2^s:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.zero_lt_of_lt i0.isLt) (pow_pos (by decide) s)
  have hu := source_uniform_of_collision i0 q hq hC
  exact ⟨q,hq,fun α hα => renyi_all_uniform q _ α hn hα hq.2.1 hu,
    minEntropy_uniform q _ hn hq.2.1 hu⟩

theorem plane_all_entropy {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    let p := uniformFiniteLaw (planeSupport hs e i0 t)
    (∀ α : ℝ, 0 < α → renyiEntropy p α = Real.log (((2^s)^2:ℕ):ℝ)) ∧
    minEntropy p = Real.log (((2^s)^2:ℕ):ℝ) := by
  classical
  let p := uniformFiniteLaw (planeSupport hs e i0 t)
  have hp : sourceFeasible i0 p := plane_uniform_feasible hk hs e he i0 t ht
  have hn : (0:ℝ) < (((2^s)^2:ℕ):ℝ) := by positivity
  have hu (y : SourceOutcome k s i0) : p y=0 ∨ p y=1/(((2^s)^2:ℕ):ℝ) := by
    dsimp [p,uniformFiniteLaw]
    split_ifs
    · exact Or.inr (by rw [planeSupport_card hk hs e i0 t ht])
    · exact Or.inl rfl
  exact ⟨fun α hα => renyi_all_uniform p _ α hn hα hp.2.1 hu,
    minEntropy_uniform p _ hn hp.2.1 hu⟩

end
end EntropyDesigns.RelativeSequence
