/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
Modified imports for bounded compilation; mathematical statements and proof bodies are unchanged. -/
module
public import EntropyDesigns.PositiveScaling
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.NoncommRing
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FunProp
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.Matrix.PosDef
@[expose] public section
set_option autoImplicit false
open scoped ComplexOrder
namespace EntropyDesigns

noncomputable def stochasticProduct {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ∏ i, ∑ j, B i j*x j

noncomputable def classicalStochasticCapacity {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) : ℝ :=
  sInf (Set.range (fun x : {x : ι → ℝ // ∀ j, 0<x j} => stochasticProduct B x.val/(∏ j, x.val j)))

theorem doubly_stochastic_product_lower {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) (hB : ∀ i j, 0≤B i j)
    (hRows : ∀ i, ∑ j, B i j=1) (hCols : ∀ j, ∑ i, B i j=1)
    (x : ι → ℝ) (hx : ∀ j, 0<x j) :
    (∏ j, x j)≤stochasticProduct B x := by
  have hWeighted (i : ι) : (∏ j, x j^(B i j))≤∑ j, B i j*x j :=
    Real.geom_mean_le_arith_mean_weighted Finset.univ (B i) x
      (fun j _ => hB i j) (hRows i) (fun j _ => (hx j).le)
  have hProd := Finset.prod_le_prod₀
    (fun i (_ : i∈(Finset.univ : Finset ι)) => Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (hx j).le _))
    (fun i (_ : i∈(Finset.univ : Finset ι)) => hWeighted i)
  have hCombine : (∏ i, ∏ j, x j^(B i j))=∏ j, x j := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    rw [← Real.rpow_sum_of_pos (hx j),hCols j,Real.rpow_one]
  rw [hCombine] at hProd
  exact hProd

theorem doubly_stochastic_classical_capacity_one {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) (hB : ∀ i j, 0≤B i j)
    (hRows : ∀ i, ∑ j, B i j=1) (hCols : ∀ j, ∑ i, B i j=1) :
    classicalStochasticCapacity B=1 := by
  let f := fun x : {x : ι → ℝ // ∀ j, 0<x j} => stochasticProduct B x.val/(∏ j, x.val j)
  have hLower (x : {x : ι → ℝ // ∀ j, 0<x j}) : 1≤f x := by
    have hden : 0<∏ j, x.val j := Finset.prod_pos (fun j _ => x.property j)
    apply (le_div_iff₀ hden).mpr
    simpa only [one_mul] using doubly_stochastic_product_lower B hB hRows hCols x.val x.property
  have hOne : (1:ℝ)∈Set.range f := by
    refine ⟨⟨fun _ => 1,fun _ => by norm_num⟩,?_⟩
    simp [f,stochasticProduct,hRows]
  have hBelow : BddBelow (Set.range f) := by
    refine ⟨1,?_⟩
    rintro z ⟨x,rfl⟩
    exact hLower x
  apply le_antisymm
  · exact csInf_le hBelow hOne
  · apply le_csInf (Set.nonempty_of_mem hOne)
    rintro z ⟨x,rfl⟩
    exact hLower x


noncomputable def unitarySquareWeights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℝ := fun i j => Complex.normSq (U.val i j)

theorem unitary_square_weights_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (i : ι) : ∑ j, unitarySquareWeights U i j=1 := by
  have hGram : U.val*U.val.conjTranspose=1 := Unitary.coe_mul_star_self U
  have h := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) hGram
  simpa [unitarySquareWeights,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.mul_re,
    Complex.normSq_apply] using h

theorem unitary_square_weights_columns {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (j : ι) : ∑ i, unitarySquareWeights U i j=1 := by
  have hGram : U.val.conjTranspose*U.val=1 := Unitary.coe_star_mul_self U
  have h := congrArg (fun M : Matrix ι ι ℂ => (M j j).re) hGram
  simpa [unitarySquareWeights,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.mul_re,
    Complex.normSq_apply] using h


theorem hermitian_spectral_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (i : ι) :
    (X i i).re=∑ j, unitarySquareWeights hX.eigenvectorUnitary i j*hX.eigenvalues j := by
  have hSpec : X=hX.eigenvectorUnitary.val*Matrix.diagonal (fun j => (hX.eigenvalues j : ℂ))*
      hX.eigenvectorUnitary.val.conjTranspose := by
    simpa only [Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose,Function.comp_def,RCLike.ofReal_eq_complex_ofReal]
      using hX.spectral_theorem
  have hEntry : X i i=∑ j, hX.eigenvectorUnitary.val i j*(hX.eigenvalues j : ℂ)*star (hX.eigenvectorUnitary.val i j) := by
    calc
      X i i=(hX.eigenvectorUnitary.val*Matrix.diagonal (fun j => (hX.eigenvalues j : ℂ))*
        hX.eigenvectorUnitary.val.conjTranspose) i i := congrArg (fun M : Matrix ι ι ℂ => M i i) hSpec
      _=_ := by simp [Matrix.mul_apply,Matrix.diagonal_apply,Matrix.conjTranspose_apply,mul_ite]
  rw [hEntry]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [unitarySquareWeights,Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
  ring

theorem complex_posdef_det_le_diagonal_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) (hX : X.PosDef) : X.det.re≤∏ i, (X i i).re := by
  let U := hX.isHermitian.eigenvectorUnitary
  let eigVals := hX.isHermitian.eigenvalues
  have heigVals : ∀ j, 0<eigVals j := hX.eigenvalues_pos
  have hDet : X.det.re=∏ j, eigVals j := by
    have h := congrArg Complex.re hX.isHermitian.det_eq_prod_eigenvalues
    simpa only [RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_prod,Complex.ofReal_re] using h
  have hLower := doubly_stochastic_product_lower (unitarySquareWeights U)
    (fun i j => Complex.normSq_nonneg _) (unitary_square_weights_rows U) (unitary_square_weights_columns U) eigVals heigVals
  rw [← hDet] at hLower
  have hDiag (i : ι) : (X i i).re=∑ j, unitarySquareWeights U i j*eigVals j :=
    hermitian_spectral_diagonal X hX.isHermitian i
  unfold stochasticProduct at hLower
  simpa only [← hDiag] using hLower


noncomputable def stochasticComplexChannel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => ∑ j, (B i j : ℂ)*X j j)

noncomputable def operatorStochasticCapacity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) : ℝ :=
  sInf (Set.range (fun X : {X : Matrix ι ι ℂ // X.PosDef} =>
    (stochasticComplexChannel B X.val).det.re/X.val.det.re))

theorem stochastic_complex_channel_unital {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hRows : ∀ i, ∑ j, B i j=1) :
    stochasticComplexChannel B (1 : Matrix ι ι ℂ)=1 := by
  have hOne (i : ι) : (∑ j, (B i j : ℂ)*(1 : Matrix ι ι ℂ) j j)=1 := by
    simpa only [Matrix.one_apply,ite_true,mul_one,← Complex.ofReal_sum,hRows,Complex.ofReal_one]
  have hSum (i : ι) : (∑ j, (B i j : ℂ))=1 := by
    rw [← Complex.ofReal_sum,hRows i,Complex.ofReal_one]
  ext i j
  simp [stochasticComplexChannel,hSum,Matrix.one_apply,Matrix.diagonal_apply]

theorem stochastic_complex_channel_det_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (X : Matrix ι ι ℂ) (hX : X.PosDef) :
    (stochasticComplexChannel B X).det.re=stochasticProduct B (fun j => (X j j).re) := by
  have hReal (j : ι) : X j j=((X j j).re : ℂ) := by
    apply Complex.ext
    · simp
    · have h := (Complex.pos_iff.mp (hX.diag_pos (i:=j))).2
      simpa using h.symm
  have hDiag : stochasticComplexChannel B X=
      Matrix.diagonal (fun i => ((∑ j, B i j*(X j j).re : ℝ) : ℂ)) := by
    unfold stochasticComplexChannel
    congr 1
    funext i
    simp only [Complex.ofReal_sum,Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hReal j]
    simp only [Complex.ofReal_re]
  rw [hDiag,Matrix.det_diagonal,← Complex.ofReal_prod,Complex.ofReal_re]
  rfl

theorem doubly_stochastic_operator_capacity_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : ∀ i j, 0≤B i j)
    (hRows : ∀ i, ∑ j, B i j=1) (hCols : ∀ j, ∑ i, B i j=1) :
    operatorStochasticCapacity B=1 := by
  let f := fun X : {X : Matrix ι ι ℂ // X.PosDef} =>
    (stochasticComplexChannel B X.val).det.re/X.val.det.re
  have hLower (X : {X : Matrix ι ι ℂ // X.PosDef}) : 1≤f X := by
    have hdet : 0<X.val.det.re := (Complex.pos_iff.mp X.property.det_pos).1
    change 1≤(stochasticComplexChannel B X.val).det.re/X.val.det.re
    apply (le_div_iff₀ hdet).mpr
    rw [one_mul,stochastic_complex_channel_det_re B X.val X.property]
    apply (complex_posdef_det_le_diagonal_product X.val X.property).trans
    exact doubly_stochastic_product_lower B hB hRows hCols (fun j => (X.val j j).re)
      (fun j => (Complex.pos_iff.mp (X.property.diag_pos (i:=j))).1)
  have hOne : (1:ℝ)∈Set.range f := by
    refine ⟨⟨1,Matrix.PosDef.one⟩,?_⟩
    simp [f,stochastic_complex_channel_unital B hRows]
  have hBelow : BddBelow (Set.range f) := by
    refine ⟨1,?_⟩
    rintro z ⟨X,rfl⟩
    exact hLower X
  apply le_antisymm
  · exact csInf_le hBelow hOne
  · apply le_csInf (Set.nonempty_of_mem hOne)
    rintro z ⟨X,rfl⟩
    exact hLower X


noncomputable def stochasticKraus {ι : Type*} [DecidableEq ι]
    (B : Matrix ι ι ℝ) (i j : ι) : Matrix ι ι ℂ := Matrix.single i j (Real.sqrt (B i j) : ℂ)

theorem stochastic_kraus_sandwich {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : ∀ i j, 0≤B i j) (X : Matrix ι ι ℂ) (i j : ι) :
    stochasticKraus B i j*X*(stochasticKraus B i j).conjTranspose=
      Matrix.single i i ((B i j : ℂ)*X j j) := by
  rw [stochasticKraus,Matrix.conjTranspose_single,Matrix.single_mul_mul_single]
  congr 1
  have hStar : star (Real.sqrt (B i j) : ℂ)=(Real.sqrt (B i j) : ℂ) := by simp
  rw [hStar]
  have hSqrt : (Real.sqrt (B i j) : ℂ)*(Real.sqrt (B i j) : ℂ)=(B i j : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (hB i j)]
  calc
    _=(Real.sqrt (B i j) : ℂ)*(Real.sqrt (B i j) : ℂ)*X j j := by ring
    _=_ := by rw [hSqrt]

theorem stochastic_complex_channel_kraus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : ∀ i j, 0≤B i j) (X : Matrix ι ι ℂ) :
    stochasticComplexChannel B X=
      ∑ i, ∑ j, stochasticKraus B i j*X*(stochasticKraus B i j).conjTranspose := by
  simp_rw [stochastic_kraus_sandwich B hB X]
  ext p q
  by_cases hpq : p=q
  · subst q
    simp [stochasticComplexChannel,Matrix.single_apply,Matrix.diagonal_apply,Matrix.sum_apply]
  · have hNo (i : ι) : ¬(i=p ∧ i=q) := by rintro ⟨rfl,h⟩; exact hpq h
    simp [stochasticComplexChannel,Matrix.single_apply,Matrix.diagonal_apply,Matrix.sum_apply,hpq,hNo]


theorem stochastic_complex_channel_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (X Y : Matrix ι ι ℂ) :
    Matrix.trace ((stochasticComplexChannel B X).conjTranspose*Y)=
      Matrix.trace (X.conjTranspose*stochasticComplexChannel B.transpose Y) := by
  simp [stochasticComplexChannel,Matrix.trace,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.diagonal_apply,mul_ite,ite_mul,map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem stochastic_complex_channel_adjoint_unital {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hCols : ∀ j, ∑ i, B i j=1) :
    stochasticComplexChannel B.transpose (1 : Matrix ι ι ℂ)=1 := by
  apply stochastic_complex_channel_unital
  intro j
  exact hCols j


theorem stochastic_kraus_amplifications_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (k : ℕ) (Y : Matrix (ι×Fin k) (ι×Fin k) ℂ) (hY : Y.PosSemidef) :
    (∑ i, ∑ j,
      (Matrix.kronecker (stochasticKraus B i j) (1 : Matrix (Fin k) (Fin k) ℂ))*Y*
        (Matrix.kronecker (stochasticKraus B i j) (1 : Matrix (Fin k) (Fin k) ℂ)).conjTranspose).PosSemidef := by
  apply Matrix.posSemidef_sum Finset.univ
  intro i _
  apply Matrix.posSemidef_sum Finset.univ
  intro j _
  exact hY.mul_mul_conjTranspose_same _

theorem doubly_stochastic_capacities_are_blind {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : ∀ i j, 0≤B i j)
    (hRows : ∀ i, ∑ j, B i j=1) (hCols : ∀ j, ∑ i, B i j=1) :
    classicalStochasticCapacity B=1 ∧ operatorStochasticCapacity B=1 ∧
    stochasticComplexChannel B (1 : Matrix ι ι ℂ)=1 ∧
    stochasticComplexChannel B.transpose (1 : Matrix ι ι ℂ)=1 ∧
    (∀ X : Matrix ι ι ℂ, stochasticComplexChannel B X=
      ∑ i, ∑ j, stochasticKraus B i j*X*(stochasticKraus B i j).conjTranspose) ∧
    (∀ X Y : Matrix ι ι ℂ, Matrix.trace ((stochasticComplexChannel B X).conjTranspose*Y)=
      Matrix.trace (X.conjTranspose*stochasticComplexChannel B.transpose Y)) ∧
    (∀ k : ℕ, ∀ Y : Matrix (ι×Fin k) (ι×Fin k) ℂ, Y.PosSemidef →
      (∑ i, ∑ j,
        (Matrix.kronecker (stochasticKraus B i j) (1 : Matrix (Fin k) (Fin k) ℂ))*Y*
          (Matrix.kronecker (stochasticKraus B i j) (1 : Matrix (Fin k) (Fin k) ℂ)).conjTranspose).PosSemidef) ∧
    (∀ U : Matrix ι ι ℝ, U*U.transpose=1 → U.transpose*U=1 →
      classicalStochasticCapacity (fun i j => U i j^2)=1 ∧
      operatorStochasticCapacity (fun i j => U i j^2)=1 ∧
      stochasticComplexChannel (fun i j => U i j^2) (1 : Matrix ι ι ℂ)=1 ∧
      stochasticComplexChannel (fun i j => U j i^2) (1 : Matrix ι ι ℂ)=1) := by
  refine ⟨doubly_stochastic_classical_capacity_one B hB hRows hCols,
    doubly_stochastic_operator_capacity_one B hB hRows hCols,
    stochastic_complex_channel_unital B hRows,stochastic_complex_channel_adjoint_unital B hCols,
    stochastic_complex_channel_kraus B hB,stochastic_complex_channel_adjoint B,
    stochastic_kraus_amplifications_positive B,?_⟩
  intro U hUR hUC
  have hs (i j : ι) : 0≤U i j^2 := sq_nonneg _
  have hr := orthogonal_diagonal_square_rows U hUR
  have hc := orthogonal_diagonal_square_columns U hUC
  exact ⟨doubly_stochastic_classical_capacity_one _ hs hr hc,
    doubly_stochastic_operator_capacity_one _ hs hr hc,
    stochastic_complex_channel_unital _ hr,stochastic_complex_channel_adjoint_unital _ hc⟩

end EntropyDesigns
