/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.CollisionRounding
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
@[expose] public section
set_option maxHeartbeats 2000000
namespace EntropyDesigns
open Filter
open scoped Topology
noncomputable section

def collisionWindowDelta (n : ℝ) : ℝ := 4/((n-1)*(n^2-4))
def collisionEntropyWindow (n : ℝ) : ℝ := -Real.log (1-collisionWindowDelta n)

theorem collisionWindowDelta_bounds {n : ℝ} (hn : 4≤n) :
    0<collisionWindowDelta n ∧ collisionWindowDelta n<1 := by
  have h1 : 3≤n-1 := by linarith
  have h2 : 12≤n^2-4 := by nlinarith
  have hD : 4<(n-1)*(n^2-4) := by nlinarith
  constructor
  · exact div_pos (by norm_num) (by nlinarith)
  · exact (div_lt_one (by nlinarith)).mpr hD

theorem collisionEntropyWindow_pos {n : ℝ} (hn : 4≤n) : 0<collisionEntropyWindow n := by
  obtain ⟨hPos,hLt⟩ := collisionWindowDelta_bounds hn
  have hLog := Real.log_neg (show 0<1-collisionWindowDelta n by linarith)
    (show 1-collisionWindowDelta n<1 by linarith)
  exact neg_pos.mpr hLog

theorem positive_entropy_window {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (hn : 4≤n) (hEven : n%2=0) (A : α → Fin n → ℤ) (hA : ∀ x i,A x i=1 ∨ A x i= -1)
    (w : α → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hiso : ∀ i j,∑ x,w x*(A x i : ℝ)*(A x j : ℝ)=if i=j then 1 else 0)
    (hEntropy : shannon w<Real.log (n : ℝ)+collisionEntropyWindow n) :
    0<collisionEntropyWindow n ∧ HasSupportedHadamard A w := by
  have hnR : (4 : ℝ)≤n := by exact_mod_cast hn
  have hnPos : (0 : ℝ)<n := by linarith
  obtain ⟨hDeltaPos,hDeltaLt⟩ := collisionWindowDelta_bounds hnR
  let c := (1-collisionWindowDelta n)/(n : ℝ)
  have hc : 0<c := div_pos (by linarith) hnPos
  have hLog : -Real.log c=Real.log (n : ℝ)+collisionEntropyWindow n := by
    dsimp only [c,collisionEntropyWindow]
    rw [Real.log_div (by linarith) hnPos.ne']
    ring
  have hEnt := shannon_ge_collision_entropy w hw hmass
  have hCpos := collision_pos w hw hmass
  have hC : c<collision w := by
    apply (Real.log_lt_log_iff hc hCpos).mp
    unfold collisionEntropy at hEnt
    linarith
  have hcEq : c=1/(n : ℝ)-4/((n : ℝ)*((n : ℝ)-1)*((n : ℝ)^2-4)) := by
    dsimp only [c,collisionWindowDelta]
    field_simp
    <;> ring
  rw [hcEq] at hC
  exact ⟨collisionEntropyWindow_pos hnR,(explicit_collision_gap hn hEven A hA w hw hmass hiso).1 hC⟩


theorem collisionWindowDelta_normalized {x : ℝ} (hx : 4≤x) :
    collisionWindowDelta x=4*(x⁻¹)^3/((1-x⁻¹)*(1-4*(x⁻¹)^2)) ∧
    collisionWindowDelta x/(4/x^3)=1/((1-x⁻¹)*(1-4*(x⁻¹)^2)) := by
  have hx0 : x≠0 := by linarith
  have hx1 : x-1≠0 := by linarith
  have hx2 : x^2-4≠0 := by nlinarith
  have hDen : (1-x⁻¹)*(1-4*(x⁻¹)^2)=(x-1)*(x^2-4)/x^3 := by
    field_simp
    <;> ring
  have hDen0 : (1-x⁻¹)*(1-4*(x⁻¹)^2)≠0 := by
    rw [hDen]
    exact div_ne_zero (mul_ne_zero hx1 hx2) (pow_ne_zero 3 hx0)
  constructor <;> unfold collisionWindowDelta <;> rw [hDen]
  · field_simp
    <;> ring
  · field_simp
    <;> ring

theorem collisionWindowDelta_tendsto_zero : Tendsto collisionWindowDelta atTop (𝓝 0) := by
  have hInv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hFour : Tendsto (fun _ : ℝ => (4 : ℝ)) atTop (𝓝 4) := tendsto_const_nhds
  have hDen := (hOne.sub hInv).mul (hOne.sub (hFour.mul (hInv.pow 2)))
  have hNum := hFour.mul (hInv.pow 3)
  have hD : Tendsto (fun x : ℝ => (1-x⁻¹)*(1-4*(x⁻¹)^2)) atTop (𝓝 1) := by
    convert hDen using 1 <;> norm_num
  have hN : Tendsto (fun x : ℝ => 4*(x⁻¹)^3) atTop (𝓝 0) := by
    convert hNum using 1 <;> norm_num
  have hQ := hN.div hD (by norm_num : (1 : ℝ)≠0)
  simp only [zero_div] at hQ
  apply hQ.congr'
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
  exact (collisionWindowDelta_normalized hx).1.symm

theorem collisionWindowDelta_relative_limit :
    Tendsto (fun x : ℝ => collisionWindowDelta x/(4/x^3)) atTop (𝓝 1) := by
  have hInv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hFour : Tendsto (fun _ : ℝ => (4 : ℝ)) atTop (𝓝 4) := tendsto_const_nhds
  have hDen := (hOne.sub hInv).mul (hOne.sub (hFour.mul (hInv.pow 2)))
  have hD : Tendsto (fun x : ℝ => (1-x⁻¹)*(1-4*(x⁻¹)^2)) atTop (𝓝 1) := by
    convert hDen using 1 <;> norm_num
  have hQ := hOne.div hD (by norm_num : (1 : ℝ)≠0)
  simp only [div_one] at hQ
  apply hQ.congr'
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
  exact (collisionWindowDelta_normalized hx).2.symm


theorem collisionEntropyWindow_relative_limit :
    Tendsto (fun x : ℝ => collisionEntropyWindow x/(4/x^3)) atTop (𝓝 1) := by
  have hf : HasDerivAt (fun t : ℝ => -Real.log (1-t)) 1 0 := by
    convert (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))).log (by norm_num)).neg using 1 <;> norm_num
    ext t
    rfl
  have hSlope : Tendsto (fun t : ℝ => -Real.log (1-t)/t) (𝓝[>] 0) (𝓝 1) := by
    simpa only [zero_add,Real.log_one,neg_zero,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using hf.tendsto_slope_zero_right
  have hWithin : Tendsto collisionWindowDelta atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨collisionWindowDelta_tendsto_zero,?_⟩
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    exact (collisionWindowDelta_bounds hx).1
  have hLog := hSlope.comp hWithin
  have hProduct := hLog.mul collisionWindowDelta_relative_limit
  simp only [one_mul] at hProduct
  apply hProduct.congr'
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
  have hDelta0 := ne_of_gt (collisionWindowDelta_bounds hx).1
  have hx0 : x≠0 := by linarith
  unfold collisionEntropyWindow
  change (-Real.log (1-collisionWindowDelta x)/collisionWindowDelta x)*
    (collisionWindowDelta x/(4/x^3))=(-Real.log (1-collisionWindowDelta x))/(4/x^3)
  field_simp



theorem collisionEntropyWindow_nat_relative_limit :
    Tendsto (fun n : ℕ => collisionEntropyWindow n/(4/(n : ℝ)^3)) atTop (𝓝 1) :=
  collisionEntropyWindow_relative_limit.comp tendsto_natCast_atTop_atTop


end
end EntropyDesigns
