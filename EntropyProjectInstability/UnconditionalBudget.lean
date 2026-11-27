/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyProjectInstability.SublinearDyadic
public import EntropyProjectArithmetic.ArithmeticInterface
@[expose] public section
namespace EntropyDesigns.ProjectInstability
open Filter Asymptotics RelativeSequence GapTransfer
open scoped Topology
noncomputable section

/-- Discharge the uniform dyadic exponent hypothesis from the licensed,
fully proved arithmetic endpoint. No distribution assumption is added. -/
theorem unconditional_uniform_dyadic_input :
    ∃ T : ℕ → ℕ,Tendsto (fun s => (T s:ℝ)/(s:ℝ)) atTop (nhds 0) ∧
      ∀ᶠ s : ℕ in atTop,∀ q : ℕ,Odd q → q≤2^s → knownHadamardOrder (2^(T s)*q) := by
  classical
  obtain ⟨C,hC,N,hN⟩ := ArithmeticInterface.uniform_exponent
  let T : ℕ → ℕ := fun s => if hs : N≤2^s then Classical.choose (hN (2^s) hs) else 0
  have hselect (s : ℕ) (hs : N≤2^s) :
      (T s:ℝ)≤C*HadamardMultibase.logScale (2^s) ∧
      ∀ q : ℕ,Odd q → q≤2^s → HadamardMultibase.HadamardOrder (2^(T s)*q) := by
    dsimp [T]
    rw [dif_pos hs]
    exact Classical.choose_spec (hN (2^s) hs)
  have hlarge : ∀ᶠ s : ℕ in atTop,N≤2^s := by
    filter_upwards [dyadic_order_tends_infinity.eventually_ge_atTop (N:ℝ)] with s hs
    exact_mod_cast hs
  have hlimit : Tendsto (fun s : ℕ => C*((Real.log ((2:ℝ)^s)/Real.log (Real.log ((2:ℝ)^s)))/(s:ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using dyadic_log_scale_ratio_zero.const_mul C
  have hratio : Tendsto (fun s => (T s:ℝ)/(s:ℝ)) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun s => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) _ hlimit
    filter_upwards [hlarge] with s hs
    calc
      (T s:ℝ)/(s:ℝ)≤(C*HadamardMultibase.logScale (2^s))/(s:ℝ) :=
        div_le_div_of_nonneg_right (hselect s hs).1 (Nat.cast_nonneg s)
      _=C*((Real.log ((2:ℝ)^s)/Real.log (Real.log ((2:ℝ)^s)))/(s:ℝ)) := by
        simp only [HadamardMultibase.logScale,Nat.cast_pow,Nat.cast_ofNat]
        ring
  refine ⟨T,hratio,?_⟩
  filter_upwards [hlarge] with s hs
  intro q hq hqs
  exact ((hselect s hs).2 q hq hqs).2

/-- An actual complete exact law at every sufficiently large dyadic seed,
with unconditional known Hadamard orders and subpolynomial omitted budget. -/
theorem unconditional_buffered_laws :
    ∃ T : ℕ → ℕ,Tendsto (fun s => (T s:ℝ)/(s:ℝ)) atTop (nhds 0) ∧
      Tendsto (fun s => ((2^s-2^(bufferExponent T s):ℕ):ℝ)/(2:ℝ)^s) atTop (nhds 1) ∧
      Tendsto (fun s => Real.log ((2:ℝ)^(bufferExponent T s))/Real.log ((2:ℝ)^s)) atTop (nhds 0) ∧
      ∀ᶠ s : ℕ in atTop,
        knownHadamardOrder (2^s-2^(bufferExponent T s)) ∧
        Nonempty (CompleteLawData (2^s-2^(bufferExponent T s)) s) ∧
        2^s-(2^s-2^(bufferExponent T s))=2^(bufferExponent T s) := by
  obtain ⟨T,hT,hu⟩ := unconditional_uniform_dyadic_input
  exact ⟨T,hT,buffered_order_ratio_one T hT,
    sublinear_dyadic_log_ratio_zero (bufferExponent T) (buffer_exponent_ratio_zero T hT),
    eventually_buffered_uniform_laws T hT hu⟩

end
end EntropyDesigns.ProjectInstability
