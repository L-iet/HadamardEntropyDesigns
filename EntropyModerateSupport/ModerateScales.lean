/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
@[expose] public section
namespace EntropyDesigns.ModerateSupport
noncomputable section

theorem linear_scale_identities (k : ℝ) (hk : 0<k) :
    (2*k)^2=2*(2*k^2) ∧
      1/(2*k)^2=1/(2*(2*k^2)) ∧
      Real.sqrt (2/(2*k^2))=1/k := by
  have hn : k≠0 := ne_of_gt hk
  refine ⟨by ring,?_,?_⟩
  · congr 1 <;> ring
  · apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    field_simp

theorem cubic_scale_identities (k : ℝ) (hk : 0<k) :
    (k^3 : ℝ)^(4/3 : ℝ)=k^4 ∧
      (k^3 : ℝ)^(-1/3 : ℝ)=1/k ∧
      (k^2)^2=k^4 ∧ k/(k^2)=1/k := by
  have hpos : 0≤k := hk.le
  refine ⟨?_,?_,by ring,?_⟩
  · calc
      (k^3 : ℝ)^(4/3 : ℝ)=(k^(3:ℝ))^(4/3:ℝ) := by norm_num
      _=k^((3:ℝ)*(4/3)) := (Real.rpow_mul hpos _ _).symm
      _=k^4 := by norm_num
  · calc
      (k^3 : ℝ)^(-1/3 : ℝ)=(k^(3:ℝ))^(-1/3:ℝ) := by norm_num
      _=k^((3:ℝ)*(-1/3)) := (Real.rpow_mul hpos _ _).symm
      _=1/k := by norm_num [Real.rpow_neg_one,one_div]
  · field_simp

end
end EntropyDesigns.ModerateSupport
