/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EscapeProof04
public import EntropyDesigns.FourBitSharpBarrier
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.NoncommRing
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FunProp
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Field
set_option Elab.async false
@[expose] public section
set_option maxHeartbeats 4000000
namespace EntropyDesigns
open Set
theorem nonnegative_slack_face_exposed {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype ι] (P : Set E) (L : ι → StrongDual ℝ E) (c : ι → ℝ)
    (hPos : ∀ x ∈ P, ∀ j, 0 ≤ c j+L j x) :
    IsExposed ℝ P {x ∈ P | ∀ j, c j+L j x=0} := by
  classical
  intro hNonempty
  obtain ⟨x0,hx0,hZero⟩ := hNonempty
  let l : StrongDual ℝ E := -(∑ j, L j)
  have hEval (x : E) : l x= -(∑ j, L j x) := by simp [l]
  have hSum0 : (∑ j, c j)+(∑ j, L j x0)=0 := by
    rw [← Finset.sum_add_distrib]
    simp only [hZero,Finset.sum_const_zero]
  refine ⟨l,?_⟩
  ext x
  constructor
  · rintro ⟨hx,hz⟩
    refine ⟨hx,?_⟩
    intro y hy
    have hSum : (∑ j, c j)+(∑ j, L j x)=0 := by
      rw [← Finset.sum_add_distrib]; simp only [hz,Finset.sum_const_zero]
    have hY : 0 ≤ (∑ j, c j)+(∑ j, L j y) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_nonneg (fun j _ => hPos y hy j)
    rw [hEval,hEval]
    linarith
  · rintro ⟨hx,hMax⟩
    refine ⟨hx,?_⟩
    have hLe := hMax x0 hx0
    rw [hEval,hEval] at hLe
    have hSum : (∑ j, (c j+L j x))=0 := by
      have hNonneg := Finset.sum_nonneg (fun j (_ : j∈Finset.univ) => hPos x hx j)
      rw [Finset.sum_add_distrib] at hNonneg ⊢
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hPos x hx j)).mp hSum |> fun h j => h j (Finset.mem_univ j)


end EntropyDesigns
