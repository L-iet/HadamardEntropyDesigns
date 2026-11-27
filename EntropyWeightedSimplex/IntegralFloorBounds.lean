/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators
open Set MeasureTheory

 theorem antitone_integral_le_floor_sum (f : ℝ → ℝ) (hf : Continuous f)
    (u : ℝ) (hu : 0≤u) (ha : AntitoneOn f (Icc 0 u))
    (hn : 0≤f (⌊u⌋₊:ℝ)) :
    (∫ x in (0:ℝ)..u,f x)≤∑ a∈Finset.range (⌊u⌋₊+1),f (a:ℝ) := by
  let M := ⌊u⌋₊
  have hM : (M:ℝ)≤u := Nat.floor_le hu
  have hMpos : (0:ℝ)≤M := Nat.cast_nonneg _
  have hfrac : u-(M:ℝ)≤1 := by
    have hh := Nat.lt_floor_add_one u
    change u<(M:ℝ)+1 at hh
    linarith
  have haM : AntitoneOn f (Icc 0 (0+(M:ℝ))) := by
    apply ha.mono
    intro x hx
    exact ⟨hx.1,by linarith [hx.2]⟩
  have hmain : (∫ x in (0:ℝ)..(M:ℝ),f x)≤∑ a∈Finset.range M,f (a:ℝ) := by
    simpa using haM.integral_le_sum
  have htail : (∫ x in (M:ℝ)..u,f x)≤f (M:ℝ) := by
    calc
      _≤∫ x in (M:ℝ)..u,f (M:ℝ) := by
        apply intervalIntegral.integral_mono_on hM (hf.intervalIntegrable _ _) (intervalIntegrable_const)
        intro x hx
        exact ha ⟨hMpos,hM⟩ ⟨hMpos.trans hx.1,hx.2⟩ hx.1
      _=(u-(M:ℝ))*f (M:ℝ) := by simp
      _≤f (M:ℝ) := by nlinarith
  have he : (∫ x in (0:ℝ)..(M:ℝ),f x)+(∫ x in (M:ℝ)..u,f x)=
      (∫ x in (0:ℝ)..u,f x) := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (0:ℝ) (M:ℝ)) (hf.intervalIntegrable (M:ℝ) u)
  rw [Finset.sum_range_succ]
  change (∫ x in (0:ℝ)..u,f x)≤(∑ a∈Finset.range M,f (a:ℝ))+f (M:ℝ)
  linarith

 theorem antitone_floor_sum_le_integral (f : ℝ → ℝ) (M : ℕ)
    (ha : AntitoneOn f (Icc (-1) (M:ℝ))) :
    (∑ a∈Finset.range (M+1),f (a:ℝ))≤∫ x in (-1:ℝ)..(M:ℝ),f x := by
  have he : (-1:ℝ)+((M+1:ℕ):ℝ)=(M:ℝ) := by push_cast;ring
  have ha' : AntitoneOn f (Icc (-1) ((-1:ℝ)+((M+1:ℕ):ℝ))) := by simpa only [he] using ha
  have hh := ha'.sum_le_integral
  have hi (a : ℕ) : (-1:ℝ)+((a+1:ℕ):ℝ)=(a:ℝ) := by push_cast;ring
  simpa only [hi,he] using hh

end EntropyDesigns.WeightedSimplex
