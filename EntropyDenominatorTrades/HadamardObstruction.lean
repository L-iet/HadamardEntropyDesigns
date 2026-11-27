/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.QuantitativeObstruction
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
noncomputable section

theorem integral_hadamard_entries_sign {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (i j : J) : A i j=1 ∨ A i j= -1 := by
  have he := Unitary.star_mul_self_of_mem (hA.apply_mem i j)
  exact mul_self_eq_one_iff.mp (by simpa only [star_trivial] using he)

theorem integral_hadamard_row_gram {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (i l : J) :
    (∑ j,A i j*A l j)=if i=l then (Fintype.card J:ℤ) else 0 := by
  have he := congrArg (fun M : Matrix J J ℤ => M i l) hA.mul_conjTranspose
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,
    Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero] using he

theorem hadamard_new_row_denominator_obstruction {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix J J ℤ) (hA : A.IsHadamard)
    (e : I ↪ J) (hr : Fintype.card I<Fintype.card J) (x : J → ℤ)
    (hx : ∀ j,x j=1 ∨ x j= -1)
    (hspan : (fun j => (x j:ℝ)) ∈ Submodule.span ℝ (Set.range (fun i j => (A (e i) j:ℝ))))
    (hnew : ∀ i,x≠A (e i) ∧ x≠fun j => -A (e i) j)
    (m : ℕ) (hm : 1<m) (hodd : Odd m) (hcard : Fintype.card J=4*m) :
    (m.minFac:ℝ)≤(Fintype.card I:ℝ)^((Fintype.card I:ℝ)/2)/(2:ℝ)^(Fintype.card I-1) ∧
    1<coefficientDenominator (orthogonalCoefficient (fun i j => A (e i) j) x) ∧
    coefficientDenominator (orthogonalCoefficient (fun i j => A (e i) j) x)∣m ∧
    (∀ c : I ↪ J,(coefficientDenominator (orthogonalCoefficient (fun i j => A (e i) j) x):ℤ)∣
      (Matrix.submatrix (fun i j => A (e i) j : Matrix I J ℤ) id c).det/(2:ℤ)^(Fintype.card I-1)) := by
  classical
  have hns : ¬Function.Surjective e := by
    intro h
    exact (not_le_of_gt hr) (Fintype.card_le_of_surjective e h)
  obtain ⟨j,hj⟩ := not_forall.mp hns
  have hout (i : I) : e i≠j := fun h => hj ⟨i,h⟩
  have hg (i l : I) : (∑ j,A (e i) j*A (e l) j)=
      if i=l then (Fintype.card J:ℤ) else 0 := by
    simpa only [EmbeddingLike.apply_eq_iff_eq] using integral_hadamard_row_gram A hA (e i) (e l)
  have ho (i : I) : (∑ k,A (e i) k*A j k)=0 := by
    simpa only [hout i,ite_false] using integral_hadamard_row_gram A hA (e i) j
  have hn : 0<Fintype.card J := by omega
  exact outside_span_sharp_denominator_bound (fun i k => A (e i) k) x (A j) hn
    (fun i k => integral_hadamard_entries_sign A hA (e i) k) hx
    (fun k => integral_hadamard_entries_sign A hA j k) hg hspan ho hnew m (by omega) hodd hcard

end
end EntropyDesigns.DenominatorTrades
