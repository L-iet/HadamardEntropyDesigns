module

public import EntropyDesigns.BoundedReduction
public import Mathlib.Analysis.Convex.Extreme

/-! # The terminal support is an actual vertex of the moment polytope -/

@[expose] public section
namespace EntropyDesigns

theorem independent_support_unique {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℝ) (p q : α → ℝ)
    (hlin : LinearIndependent ℝ (A.submatrix id (fun a : activeSupport p => (a : α))).col)
    (hsupport : ∀ a, a ∉ activeSupport p → q a = 0)
    (hfeasible : A.mulVec q = A.mulVec p) : q = p := by
  classical
  let S := activeSupport p
  have hp : extendWeights S (fun a => p a) = p := extendWeights_restrict S p (by
    intro a ha
    simpa [S, activeSupport] using ha)
  have hq : extendWeights S (fun a => q a) = q := extendWeights_restrict S q hsupport
  have hrestricted : (A.submatrix id (fun a : S => (a : α))).mulVec (fun a => q a) =
      (A.submatrix id (fun a : S => (a : α))).mulVec (fun a => p a) := by
    rw [← matrix_extendWeights, ← matrix_extendWeights, hq, hp]
    exact hfeasible
  have hvalues := (Matrix.mulVec_injective_iff.mpr hlin) hrestricted
  exact hq.symm.trans ((congrArg (extendWeights S) hvalues).trans hp)

theorem independent_support_vertex {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ)
    (hp : feasibleLaw A b p)
    (hlin : LinearIndependent ℝ (A.submatrix id (fun a : activeSupport p => (a : α))).col) :
    p ∈ Set.extremePoints ℝ {q | feasibleLaw A b q} := by
  classical
  refine ⟨hp, ?_⟩
  intro x hx y hy hsegment
  obtain ⟨a, c, ha, hc, hac, hcombo⟩ := hsegment
  apply independent_support_unique A p x hlin ?_ (hx.2.2.trans hp.2.2.symm)
  intro j hj
  have hpj : p j = 0 := by simpa [activeSupport] using hj
  have h := congrFun hcombo j
  change a * x j + c * y j = p j at h
  have hnonneg : 0 ≤ c * y j := mul_nonneg hc.le (hy.1 j)
  have hxj := hx.1 j
  have hxzero : a * x j = 0 := by nlinarith
  exact (mul_eq_zero.mp hxzero).resolve_left ha.ne'

end EntropyDesigns
