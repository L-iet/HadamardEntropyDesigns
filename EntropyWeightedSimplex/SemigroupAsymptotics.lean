/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyWeightedSimplex.SemigroupSimplex
public import EntropyWeightedSimplex.SimplexRelativeError
@[expose] public section
namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Topology
open Filter

noncomputable def simplexDenominator {r : ℕ} (b : Fin r → ℕ) : ℝ :=
  (r.factorial:ℝ)*(∏ i,Real.log (b i:ℝ))

noncomputable def simplexShift {r : ℕ} (b : Fin r → ℕ) : ℝ :=
  ∑ i,Real.log (b i:ℝ)

noncomputable def simplexLeadingCoefficient {r : ℕ} (b : Fin r → ℕ) : ℝ :=
  1/simplexDenominator b

 theorem simplex_denominator_positive {r : ℕ} (b : Fin r → ℕ) (hb : ∀ i,2≤b i) :
    0<simplexDenominator b := by
  apply mul_pos (by exact_mod_cast Nat.factorial_pos r)
  apply Finset.prod_pos
  intro i _
  apply Real.log_pos
  exact_mod_cast (show 1<b i by have hh := hb i;omega)

 theorem simplex_shift_nonnegative {r : ℕ} (b : Fin r → ℕ) (hb : ∀ i,2≤b i) :
    0≤simplexShift b := by
  apply Finset.sum_nonneg
  intro i _
  apply Real.log_nonneg
  exact_mod_cast (show 1≤b i by have hh := hb i;omega)

 theorem power_count_relative_error_isBigO {r : ℕ} (hr : 1≤r) (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) :
    (fun N : ℝ => (powerCount b N:ℝ)/(simplexLeadingCoefficient b*(Real.log N)^r)-1)
      =O[atTop] (fun N : ℝ => 1/Real.log N) := by
  have h := relative_simplex_error_isBigO (fun L : ℝ => (powerCount b (Real.exp L):ℝ)) r hr
    (simplexShift b) (simplexDenominator b) (simplex_shift_nonnegative b hb)
    (simplex_denominator_positive b hb)
    (fun L hL => power_product_simplex_bounds b hb hind L hL)
  have hcomp := h.comp_tendsto Real.tendsto_log_atTop
  apply hcomp.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with N hN
  simp [Real.exp_log hN,simplexLeadingCoefficient,div_eq_mul_inv,mul_comm]

 theorem power_count_asymptotic {r : ℕ} (hr : 1≤r) (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) :
    ∃ error : ℝ → ℝ,error =O[atTop] (fun N : ℝ => 1/Real.log N) ∧
      ∀ᶠ N : ℝ in atTop,(powerCount b N:ℝ)=
        simplexLeadingCoefficient b*(Real.log N)^r*(1+error N) := by
  let error := fun N : ℝ => (powerCount b N:ℝ)/(simplexLeadingCoefficient b*(Real.log N)^r)-1
  refine ⟨error,power_count_relative_error_isBigO hr b hb hind,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ)] with N hN
  have hD := simplex_denominator_positive b hb
  have hA : simplexLeadingCoefficient b≠0 := one_div_ne_zero hD.ne'
  have hlog : Real.log N≠0 := (Real.log_pos hN).ne'
  dsimp [error]
  field_simp <;> ring

end EntropyDesigns.WeightedSimplex
