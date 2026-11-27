/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySpanningSlopes.NormalizedColumns
public import EntropyDesigns.BinaryObservables
public import EntropyConcentratedFamily.GlobalCap
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SpanningSlopes
noncomputable section
open SupportFace
open scoped BigOperators

def normalizedHadamardLaw {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix (Option α) (Option α) ℤ) : (α → Bool) → ℝ :=
  pushLaw (normalizedRowCode A) (fun _ => 1/(Fintype.card (Option α):ℝ))

theorem normalized_hadamard_source_feasible {k s : ℕ} (i0 : Fin k)
    (A : Matrix (Option (SourceCoordinate k s i0)) (Option (SourceCoordinate k s i0)) ℤ)
    (hA : Matrix.IsHadamard A) (hcol : ∀ r,A r none=1) :
    sourceFeasible i0 (normalizedHadamardLaw A) := by
  classical
  have hn : (Fintype.card (Option (SourceCoordinate k s i0)):ℝ)≠0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨pushLaw_nonneg _ _ (fun _ => by positivity),?_,?_,?_⟩
  · rw [normalizedHadamardLaw,pushLaw_mass]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    simpa only [one_div] using mul_inv_cancel₀ hn
  · intro c
    change (∑ y,pushLaw (normalizedRowCode A)
      (fun _ => 1/(Fintype.card (Option (SourceCoordinate k s i0)):ℝ)) y*(bitSign (y c):ℝ))=0
    have hm := pushLaw_moment (α:=Option (SourceCoordinate k s i0)) (β:=SourceOutcome k s i0)
      (normalizedRowCode A) (fun _ => 1/(Fintype.card (Option (SourceCoordinate k s i0)):ℝ))
      (fun y => (bitSign (y c):ℝ))
    rw [hm]
    simp only [normalizedRowCode_sign A hA]
    rw [←Finset.mul_sum]
    have hc : (∑ r : Option (SourceCoordinate k s i0),(A r (some c):ℝ))=0 := by
      exact_mod_cast normalized_hadamard_column_sum A hA hcol c
    rw [hc,mul_zero]
  · intro c d hcd
    change (∑ y,pushLaw (normalizedRowCode A)
      (fun _ => 1/(Fintype.card (Option (SourceCoordinate k s i0)):ℝ)) y*
        (bitSign (y c):ℝ)*(bitSign (y d):ℝ))=0
    simp only [mul_assoc]
    have hm := pushLaw_moment (α:=Option (SourceCoordinate k s i0)) (β:=SourceOutcome k s i0)
      (normalizedRowCode A) (fun _ => 1/(Fintype.card (Option (SourceCoordinate k s i0)):ℝ))
      (fun y => (bitSign (y c):ℝ)*(bitSign (y d):ℝ))
    rw [hm]
    simp only [normalizedRowCode_sign A hA,←Int.cast_mul]
    rw [←Finset.mul_sum]
    have hc : (∑ r : Option (SourceCoordinate k s i0),(A r (some c)*A r (some d):ℤ))=0 :=
      normalized_hadamard_column_pair A hA c d hcd
    have hreal : (∑ r : Option (SourceCoordinate k s i0),((A r (some c)*A r (some d):ℤ):ℝ))=0 := by
      exact_mod_cast hc
    rw [hreal,mul_zero]

theorem normalized_hadamard_collision {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix (Option α) (Option α) ℤ) (hA : Matrix.IsHadamard A)
    (hcol : ∀ r,A r none=1) :
    collision (normalizedHadamardLaw A)=1/(Fintype.card (Option α):ℝ) := by
  classical
  have hn : (Fintype.card (Option α):ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [normalizedHadamardLaw,pushLaw_injective_collision _ (normalizedRowCode_injective A hA hcol)]
  simp only [collision,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

theorem normalized_hadamard_source_optimizer {k s : ℕ} (i0 : Fin k)
    (A : Matrix (Option (SourceCoordinate k s i0)) (Option (SourceCoordinate k s i0)) ℤ)
    (hA : Matrix.IsHadamard A) (hcol : ∀ r,A r none=1) :
    ∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
      (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) := by
  have hc : collision (normalizedHadamardLaw A)=1/((k*2^s:ℕ):ℝ) := by
    rw [normalized_hadamard_collision A hA hcol,ConcentratedFamily.augmented_coordinate_card]
  refine ⟨normalizedHadamardLaw A,normalized_hadamard_source_feasible i0 A hA hcol,hc,?_⟩
  intro w hw
  rw [hc]
  exact ConcentratedFamily.source_global_collision_cap i0 w hw

end
end EntropyDesigns.SpanningSlopes
