/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentration.PairFeatures
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.Concentration
noncomputable section
open SupportFace
open scoped BigOperators

def pairFeature {k s : ℕ} {i0 : Fin k} (i j : Fin k) (P : PairMask s)
    (y : SourceOutcome k s i0) : ℝ := blockFeature i P.1 y*blockFeature j P.2 y

def pairKernel {k s : ℕ} {i0 : Fin k} (i j : Fin k) (v : PairSeed s)
    (y : SourceOutcome k s i0) : ℝ :=
  (1/((2:ℝ)^s)^2)*(∑ P : PairMask s,pairChar P v*pairFeature i j P y)

theorem signed_pairChar {s : ℕ} (P : PairMask s) (v : PairSeed s) :
    pairChar P v=1 ∨ pairChar P v= -1 := by
  rcases walshChar_sign P.1 v.1 with h|h <;>
    rcases walshChar_sign P.2 v.2 with h'|h' <;> norm_num [pairChar,h,h']

theorem pairFeature_sign {k s : ℕ} {i0 : Fin k} (i j : Fin k) (P : PairMask s)
    (y : SourceOutcome k s i0) : pairFeature i j P y=1 ∨ pairFeature i j P y= -1 := by
  rcases blockFeature_sign i P.1 y with h|h <;>
    rcases blockFeature_sign j P.2 y with h'|h' <;> norm_num [pairFeature,h,h']

theorem pairKernel_bound {k s : ℕ} {i0 : Fin k} (i j : Fin k) (v : PairSeed s)
    (y : SourceOutcome k s i0) : |pairKernel i j v y|≤1 := by
  classical
  have hterm (P : PairMask s) : |pairChar P v*pairFeature i j P y|=1 := by
    rcases signed_pairChar P v with h|h <;>
      rcases pairFeature_sign i j P y with h'|h' <;> norm_num [h,h']
  have hsum : |∑ P : PairMask s,pairChar P v*pairFeature i j P y|≤((2:ℝ)^s)^2 := by
    calc
      _≤∑ P : PairMask s,|pairChar P v*pairFeature i j P y| := Finset.abs_sum_le_sum_abs _ _
      _=((2:ℝ)^s)^2 := by simp only [hterm];simp [PairMask,pow_two]
  have hden : ((2:ℝ)^s)^2≠0 := pow_ne_zero 2 (pow_ne_zero s (by norm_num))
  unfold pairKernel
  rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤1/((2:ℝ)^s)^2)]
  calc
    _≤(1/((2:ℝ)^s)^2)*((2:ℝ)^s)^2 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _=1 := by field_simp

theorem pairKernel_source {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (i j : Fin k) (v : PairSeed s) (x : BlockSeeds k s) :
    pairKernel i j v (sourceCode e i0 x)=if v=(x i,x j) then 1 else 0 := by
  classical
  have hfeature (P : PairMask s) : pairFeature i j P (sourceCode e i0 x)=pairChar P (x i,x j) := by
    unfold pairFeature
    rw [blockFeature_source,blockFeature_source]
    rfl
  unfold pairKernel
  simp_rw [hfeature]
  rw [pairChar_dual_orthogonality]
  have hden : ((2:ℝ)^s)^2≠0 := pow_ne_zero 2 (pow_ne_zero s (by norm_num))
  by_cases h : v=(x i,x j)
  · simp only [h,ite_true]
    field_simp
  · simp [h]

end
end EntropyDesigns.Concentration
