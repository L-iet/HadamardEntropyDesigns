/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.SourceConsequences
public import EntropyDesigns.FrameCapEquality
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.ConcentratedFamily
noncomputable section
open SupportFace
open scoped BigOperators

def sourceFrame {k s : ℕ} (i0 : Fin k) (y : SourceOutcome k s i0) :
    Option (SourceCoordinate k s i0) → ℝ := fun z => Option.elim z 1 (fun c => (bitSign (y c):ℝ))

theorem sourceFrame_sign {k s : ℕ} (i0 : Fin k) (y : SourceOutcome k s i0)
    (z : Option (SourceCoordinate k s i0)) : sourceFrame i0 y z=1 ∨ sourceFrame i0 y z= -1 := by
  rcases z with _|z
  · exact Or.inl rfl
  · cases y z <;> norm_num [sourceFrame,bitSign]

theorem sourceFrame_isotropic {k s : ℕ} (i0 : Fin k) (q : SourceOutcome k s i0 → ℝ)
    (hq : sourceFeasible i0 q) :
    ∀ a b : Option (SourceCoordinate k s i0),
      (∑ y,q y*sourceFrame i0 y a*sourceFrame i0 y b)=if a=b then 1 else 0 := by
  classical
  intro a b
  rcases a with _|a <;> rcases b with _|b
  · simpa [sourceFrame] using hq.2.1
  · simpa [sourceFrame] using hq.2.2.1 b
  · simpa [sourceFrame] using hq.2.2.1 a
  · by_cases hab : a=b
    · subst b
      have hs (y : SourceOutcome k s i0) : (bitSign (y a):ℝ)*(bitSign (y a):ℝ)=1 := by
        cases y a <;> norm_num [bitSign]
      simpa [sourceFrame,mul_assoc,hs] using hq.2.1
    · simpa [sourceFrame,hab] using hq.2.2.2 a b hab

theorem augmented_coordinate_card {k s : ℕ} (i0 : Fin k) :
    Fintype.card (Option (SourceCoordinate k s i0))=k*2^s := by
  have hn : 0<k*2^s := Nat.mul_pos (Nat.zero_lt_of_lt i0.isLt) (pow_pos (by decide) s)
  simp only [Fintype.card_option,card_source_coordinates]
  omega

theorem source_global_atom_cap {k s : ℕ} (i0 : Fin k) (q : SourceOutcome k s i0 → ℝ)
    (hq : sourceFeasible i0 q) : ∀ y,q y≤1/((k*2^s:ℕ):ℝ) := by
  classical
  have h := finite_frame_atom_cap (sourceFrame i0) q (sourceFrame_sign i0) hq.1
    (sourceFrame_isotropic i0 q hq)
  simpa only [augmented_coordinate_card i0] using h

theorem source_global_collision_cap {k s : ℕ} (i0 : Fin k) (q : SourceOutcome k s i0 → ℝ)
    (hq : sourceFeasible i0 q) : collision q≤1/((k*2^s:ℕ):ℝ) :=
  collision_le_of_atom_bound q _ hq.1 hq.2.1 (source_global_atom_cap i0 q hq)

end
end EntropyDesigns.ConcentratedFamily
