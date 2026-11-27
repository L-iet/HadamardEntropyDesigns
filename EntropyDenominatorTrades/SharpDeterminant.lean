/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.SignDeterminant
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
open Matrix
noncomputable section

theorem nonnegative_product_le_mean_power {I : Type*} [Fintype I]
    (z : I → ℝ) (hz : ∀ i,0≤z i) (hI : 0<Fintype.card I) :
    (∏ i,z i)≤((∑ i,z i)/(Fintype.card I:ℝ))^(Fintype.card I) := by
  have hr : (0:ℝ)<Fintype.card I := by exact_mod_cast hI
  have hm := Real.geom_mean_le_arith_mean (Finset.univ : Finset I)
    (fun _ => (1:ℝ)) z (fun _ _ => by norm_num) (by simpa using hr) (fun i _ => hz i)
  simp only [Real.rpow_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,one_mul] at hm
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => hz i)) _) hm (Fintype.card I)
  rw [Real.rpow_inv_natCast_pow (Finset.prod_nonneg (fun i _ => hz i)) hI.ne'] at hp
  exact hp

theorem psd_determinant_le_trace_mean_power {I : Type*} [Fintype I] [DecidableEq I]
    (G : Matrix I I ℝ) (hG : G.PosSemidef) (hI : 0<Fintype.card I) :
    G.det≤(G.trace/(Fintype.card I:ℝ))^(Fintype.card I) := by
  rw [hG.isHermitian.det_eq_prod_eigenvalues,hG.isHermitian.trace_eq_sum_eigenvalues]
  exact nonnegative_product_le_mean_power _ (fun i => hG.eigenvalues_nonneg i) hI

/-- The sharp Hadamard determinant inequality specialized to real sign matrices,
derived from spectral positivity and finite AM-GM. -/
theorem real_sign_determinant_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (pivot : I)
    (hA : ∀ i j,A i j=1 ∨ A i j= -1) :
    |A.det|≤(Fintype.card I:ℝ)^((Fintype.card I:ℝ)/2) := by
  have hI : 0<Fintype.card I := Fintype.card_pos_iff.mpr ⟨pivot⟩
  have hr : (0:ℝ)<Fintype.card I := by exact_mod_cast hI
  let G : Matrix I I ℝ := A*A.transpose
  have hG : G.PosSemidef := by
    simpa only [G,Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose A
  have hd (i : I) : G i i=(Fintype.card I:ℝ) := by
    dsimp [G]
    rw [Matrix.mul_apply]
    have he (j : I) : A i j*A i j=(1:ℝ) := by
      rcases hA i j with h|h <;> rw [h] <;> norm_num
    simp only [Matrix.transpose_apply,he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  have ht : G.trace=(Fintype.card I:ℝ)*(Fintype.card I:ℝ) := by
    simp only [Matrix.trace,Matrix.diag_apply,hd,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hdet : G.det=A.det^2 := by
    dsimp [G]
    rw [Matrix.det_mul,Matrix.det_transpose,pow_two]
  have hm : G.trace/(Fintype.card I:ℝ)=(Fintype.card I:ℝ) := by
    rw [ht]
    field_simp
  have hb := psd_determinant_le_trace_mean_power G hG hI
  rw [hdet,hm] at hb
  calc
    |A.det|=Real.sqrt (A.det^2) := (Real.sqrt_sq_eq_abs _).symm
    _≤Real.sqrt ((Fintype.card I:ℝ)^(Fintype.card I)) := Real.sqrt_le_sqrt hb
    _=(Fintype.card I:ℝ)^((Fintype.card I:ℝ)/2) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_natCast (Fintype.card I:ℝ) (Fintype.card I),
        ←Real.rpow_mul hr.le]
      congr 1
      ring

theorem integer_sign_determinant_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (pivot : I)
    (hA : ∀ i j,A i j=1 ∨ A i j= -1) :
    |(A.det:ℝ)|≤(Fintype.card I:ℝ)^((Fintype.card I:ℝ)/2) := by
  let B : Matrix I I ℝ := A.map (Int.castRingHom ℝ)
  have hs (i j : I) : B i j=1 ∨ B i j= -1 := by
    rcases hA i j with h|h <;> simp [B,Matrix.map_apply,h]
  have hb := real_sign_determinant_bound B pivot hs
  have he : B.det=(A.det:ℝ) := (Int.cast_det A).symm
  rw [he] at hb
  exact hb

theorem normalized_integer_anchor_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (pivot : I)
    (hA : ∀ i j,A i j=1 ∨ A i j= -1) :
    ∃ z : ℤ,A.det=(2:ℤ)^(Fintype.card I-1)*z ∧
      |(z:ℝ)|≤(Fintype.card I:ℝ)^((Fintype.card I:ℝ)/2)/(2:ℝ)^(Fintype.card I-1) := by
  obtain ⟨B,hB⟩ := normalized_anchor_determinant A pivot hA
  refine ⟨B.det,hB,?_⟩
  have hh : (0:ℝ)<(2:ℝ)^(Fintype.card I-1) := pow_pos (by norm_num) _
  have hb := integer_sign_determinant_bound A pivot hA
  have hc : (A.det:ℝ)=(2:ℝ)^(Fintype.card I-1)*(B.det:ℝ) := by exact_mod_cast hB
  rw [hc,abs_mul,abs_of_pos hh] at hb
  exact (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hb)

end
end EntropyDesigns.DenominatorTrades
