/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyRelativeSequence.LogarithmIndependence
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
@[expose] public section
namespace EntropyDesigns.RelativeSequence

/-- Positive powers of twelve are dense modulo the logarithm of two.
This is a density statement only; selecting orders with the required
integer gap is a separate obligation. -/
theorem dense_twelve_log_rotation :
    DenseRange (fun n : ℕ => n • (Real.log 12 : AddCircle (Real.log 2))) := by
  letI : Fact (0 < Real.log (2 : ℝ)) := ⟨Real.log_pos (by norm_num)⟩
  apply denseRange_zsmul_iff_nsmul.mp
  exact AddCircle.denseRange_zsmul_coe_iff.mpr irrational_log_twelve_div_log_two

/-- Density persists after discarding any finite initial segment. -/
theorem dense_twelve_log_rotation_tail (N : ℕ) :
    DenseRange (fun n : ℕ => (n + N) • (Real.log 12 : AddCircle (Real.log 2))) := by
  let x : AddCircle (Real.log 2) := (Real.log 12 : ℝ)
  have hs : Function.Surjective (fun y : AddCircle (Real.log 2) => y + N • x) := by
    intro y
    exact ⟨y - N • x, sub_add_cancel y (N • x)⟩
  have hd := hs.denseRange.comp dense_twelve_log_rotation
    (continuous_id.add continuous_const)
  simpa only [Function.comp_def, add_nsmul] using hd

end EntropyDesigns.RelativeSequence
