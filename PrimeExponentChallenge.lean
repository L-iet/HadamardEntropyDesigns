/- Copyright (c) 2026 Joshua Mark. Apache-2.0. Independent mathlib-only specification; intentional theorem placeholders only. -/
module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Choose
public import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.Push
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Prime.Infinite
@[expose] public section

namespace EntropyDesigns.DenominatorTrades
open Matrix
noncomputable section

theorem sign_difference_twice_half {a b : ℤ}
    (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) :
    a-b=2*((a-b)/2) := by
  sorry

theorem normalized_anchor_determinant {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (pivot : I)
    (hA : ∀ i j,A i j=1 ∨ A i j= -1) :
    ∃ B : Matrix I I ℤ,A.det=(2:ℤ)^(Fintype.card I-1)*B.det := by
  sorry

theorem normalized_sign_determinant_dvd {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (pivot : I)
    (hA : ∀ i j,A i j=1 ∨ A i j= -1) :
    (2:ℤ)^(Fintype.card I-1)∣A.det := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
open Matrix
noncomputable section

theorem nonnegative_product_le_mean_power {I : Type*} [Fintype I]
    (z : I → ℝ) (hz : ∀ i,0≤z i) (hI : 0<Fintype.card I) :
    (∏ i,z i)≤((∑ i,z i)/(Fintype.card I:ℝ))^(Fintype.card I) := by
  sorry

theorem psd_determinant_le_trace_mean_power {I : Type*} [Fintype I] [DecidableEq I]
    (G : Matrix I I ℝ) (hG : G.PosSemidef) (hI : 0<Fintype.card I) :
    G.det≤(G.trace/(Fintype.card I:ℝ))^(Fintype.card I) := by
  sorry

theorem real_sign_determinant_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (pivot : I)
    (hA : ∀ i j,A i j=1 ∨ A i j= -1) :
    |A.det|≤(Fintype.card I:ℝ)^((Fintype.card I:ℝ)/2) := by
  sorry

theorem integer_sign_determinant_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (pivot : I)
    (hA : ∀ i j,A i j=1 ∨ A i j= -1) :
    |(A.det:ℝ)|≤(Fintype.card I:ℝ)^((Fintype.card I:ℝ)/2) := by
  sorry

theorem normalized_integer_anchor_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (pivot : I)
    (hA : ∀ i j,A i j=1 ∨ A i j= -1) :
    ∃ z : ℤ,A.det=(2:ℤ)^(Fintype.card I-1)*z ∧
      |(z:ℝ)|≤(Fintype.card I:ℝ)^((Fintype.card I:ℝ)/2)/(2:ℝ)^(Fintype.card I-1) := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
noncomputable section

def coefficientDenominator {I : Type*} [Fintype I] (a : I → ℚ) : ℕ :=
  Finset.univ.lcm (fun i => (a i).den)

theorem coefficient_denominator_positive {I : Type*} [Fintype I] (a : I → ℚ) :
    0<coefficientDenominator a := by
  sorry

theorem rational_denominator_dvd_integer_multiple (x : ℚ) (D : ℕ)
    (h : ∃ z : ℤ,(D:ℚ)*x=(z:ℚ)) : x.den∣D := by
  sorry

theorem coefficient_denominator_dvd {I : Type*} [Fintype I]
    (a : I → ℚ) (D : ℕ) (h : ∀ i,∃ z : ℤ,(D:ℚ)*a i=(z:ℚ)) :
    coefficientDenominator a∣D := by
  sorry

theorem coefficient_denominator_clears {I : Type*} [Fintype I]
    (a : I → ℚ) (i : I) :
    ∃ z : ℤ,(coefficientDenominator a:ℚ)*a i=(z:ℚ) := by
  sorry

theorem coefficient_denominator_eq_one_iff {I : Type*} [Fintype I]
    (a : I → ℚ) :
    coefficientDenominator a=1 ↔ ∀ i,∃ z : ℤ,a i=(z:ℚ) := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
noncomputable section

def IsSignedCoordinate {I : Type*} [DecidableEq I] (a : I → ℚ) : Prop :=
  ∃ j : I,∃ e : ℤ,(e=1 ∨ e= -1) ∧ ∀ i,a i=if i=j then (e:ℚ) else 0

theorem integer_unit_vector_classification {I : Type*} [Fintype I] [DecidableEq I]
    (z : I → ℤ) (hsum : (∑ i,(z i)^2)=1) :
    ∃ j : I,(z j=1 ∨ z j= -1) ∧ ∀ i,i≠j → z i=0 := by
  sorry

theorem denominator_one_unit_is_signed_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℚ) (hsum : (∑ i,(a i)^2)=1) (hden : coefficientDenominator a=1) :
    IsSignedCoordinate a := by
  sorry

theorem noncoordinate_unit_denominator_gt_one {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℚ) (hsum : (∑ i,(a i)^2)=1) (hnot : ¬IsSignedCoordinate a) :
    1<coefficientDenominator a := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
open Matrix
open scoped Matrix
noncomputable section

theorem rational_denominator_dvd_int_multiple (x : ℚ) (D : ℤ)
    (h : ∃ z : ℤ,(D:ℚ)*x=(z:ℚ)) : (x.den:ℤ)∣D := by
  sorry

theorem coefficient_denominator_int_dvd {I : Type*} [Fintype I]
    (a : I → ℚ) (D : ℤ) (h : ∀ i,∃ z : ℤ,(D:ℚ)*a i=(z:ℚ)) :
    (coefficientDenominator a:ℤ)∣D := by
  sorry

theorem integer_anchor_clears_coefficients {I : Type*} [Fintype I] [DecidableEq I]
    (S : Matrix I I ℤ) (a : I → ℚ) (x : I → ℤ)
    (h : (fun i j => (S i j:ℚ))*ᵥa=fun i => (x i:ℚ)) (i : I) :
    ∃ z : ℤ,(S.det:ℚ)*a i=(z:ℚ) := by
  sorry

theorem integer_anchor_denominator_divides {I : Type*} [Fintype I] [DecidableEq I]
    (S : Matrix I I ℤ) (a : I → ℚ) (x : I → ℤ)
    (h : (fun i j => (S i j:ℚ))*ᵥa=fun i => (x i:ℚ)) :
    (coefficientDenominator a:ℤ)∣S.det := by
  sorry

theorem odd_denominator_divides_normalized_anchor {I : Type*} [Fintype I] [DecidableEq I]
    (S : Matrix I I ℤ) (pivot : I) (hS : ∀ i j,S i j=1 ∨ S i j= -1)
    (a : I → ℚ) (x : I → ℤ)
    (h : (fun i j => (S i j:ℚ))*ᵥa=fun i => (x i:ℚ))
    (hq : Odd (coefficientDenominator a)) :
    (coefficientDenominator a:ℤ)∣S.det/(2:ℤ)^(Fintype.card I-1) := by
  sorry

theorem odd_anchor_denominator_bound {I : Type*} [Fintype I] [DecidableEq I]
    (S : Matrix I I ℤ) (pivot : I) (hS : ∀ i j,S i j=1 ∨ S i j= -1)
    (a : I → ℚ) (x : I → ℤ)
    (h : (fun i j => (S i j:ℚ))*ᵥa=fun i => (x i:ℚ))
    (hq : Odd (coefficientDenominator a)) (hdet : S.det≠0) :
    (coefficientDenominator a:ℝ)≤
      (Fintype.card I:ℝ)^((Fintype.card I:ℝ)/2)/(2:ℝ)^(Fintype.card I-1) := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
noncomputable section

def positiveSignIndicator (z : ℤ) : ℤ := if z=1 then 1 else 0

theorem sign_indicator_identity {z : ℤ} (hz : z=1 ∨ z= -1) :
    z=2*positiveSignIndicator z-1 := by
  sorry

theorem sign_sum_indicator_identity {I : Type*} [Fintype I] (u : I → ℤ)
    (hu : ∀ i,u i=1 ∨ u i= -1) :
    (∑ i,u i)=2*(∑ i,positiveSignIndicator (u i))-(Fintype.card I:ℤ) := by
  sorry

theorem balanced_sign_dot_identity {I : Type*} [Fintype I]
    (u v : I → ℤ) (hu : ∀ i,u i=1 ∨ u i= -1) (hv : ∀ i,v i=1 ∨ v i= -1)
    (huz : (∑ i,u i)=0) (hvz : (∑ i,v i)=0) :
    (∑ i,u i*v i)=4*(∑ i,positiveSignIndicator (u i)*positiveSignIndicator (v i))-(Fintype.card I:ℤ) := by
  sorry

theorem balanced_sign_dot_divisible_four {I : Type*} [Fintype I]
    (u v : I → ℤ) (hu : ∀ i,u i=1 ∨ u i= -1) (hv : ∀ i,v i=1 ∨ v i= -1)
    (huz : (∑ i,u i)=0) (hvz : (∑ i,v i)=0)
    (m : ℕ) (hcard : Fintype.card I=4*m) :
    (4:ℤ)∣(∑ i,u i*v i) := by
  sorry

theorem balanced_inner_coefficient_clears {I : Type*} [Fintype I]
    (u v : I → ℤ) (hu : ∀ i,u i=1 ∨ u i= -1) (hv : ∀ i,v i=1 ∨ v i= -1)
    (huz : (∑ i,u i)=0) (hvz : (∑ i,v i)=0)
    (m : ℕ) (hm : 0<m) (hcard : Fintype.card I=4*m) :
    ∃ z : ℤ,(m:ℚ)*(((∑ i,u i*v i:ℤ):ℚ)/(Fintype.card I:ℚ))=(z:ℚ) := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
noncomputable section

def orthogonalCoefficient {I J : Type*} [Fintype J]
    (H : Matrix I J ℤ) (x : J → ℤ) (i : I) : ℚ :=
  ((∑ j,x j*H i j:ℤ):ℚ)/(Fintype.card J:ℚ)

theorem real_representation_dot {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (H : Matrix I J ℤ) (x : J → ℤ) (b : I → ℝ)
    (hgram : ∀ i l,(∑ j,H i j*H l j)=if i=l then (Fintype.card J:ℤ) else 0)
    (hrep : ∀ j,(x j:ℝ)=∑ i,b i*(H i j:ℝ)) (i : I) :
    (∑ j,(x j:ℝ)*(H i j:ℝ))=(Fintype.card J:ℝ)*b i := by
  sorry

theorem real_coefficient_eq_rational {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (H : Matrix I J ℤ) (x : J → ℤ) (b : I → ℝ)
    (hn : 0<Fintype.card J)
    (hgram : ∀ i l,(∑ j,H i j*H l j)=if i=l then (Fintype.card J:ℤ) else 0)
    (hrep : ∀ j,(x j:ℝ)=∑ i,b i*(H i j:ℝ)) (i : I) :
    b i=(orthogonalCoefficient H x i:ℝ) := by
  sorry

theorem rational_expansion_of_real_representation {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I]
    (H : Matrix I J ℤ) (x : J → ℤ) (b : I → ℝ)
    (hn : 0<Fintype.card J)
    (hgram : ∀ i l,(∑ j,H i j*H l j)=if i=l then (Fintype.card J:ℤ) else 0)
    (hrep : ∀ j,(x j:ℝ)=∑ i,b i*(H i j:ℝ)) :
    ∀ j,(x j:ℚ)=∑ i,orthogonalCoefficient H x i*(H i j:ℚ) := by
  sorry

theorem rational_sign_coefficients_unit {I J : Type*} [Fintype I] [Fintype J]
    (H : Matrix I J ℤ) (x : J → ℤ) (hn : 0<Fintype.card J)
    (hx : ∀ j,x j=1 ∨ x j= -1)
    (hrep : ∀ j,(x j:ℚ)=∑ i,orthogonalCoefficient H x i*(H i j:ℚ)) :
    (∑ i,(orthogonalCoefficient H x i)^2)=(1:ℚ) := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
noncomputable section

theorem represented_common_orthogonal {I J : Type*} [Fintype I] [Fintype J]
    (H : Matrix I J ℤ) (x w : J → ℤ) (b : I → ℝ)
    (hrep : ∀ j,(x j:ℝ)=∑ i,b i*(H i j:ℝ))
    (hw : ∀ i,(∑ j,H i j*w j)=0) : (∑ j,x j*w j)=0 := by
  sorry

theorem sign_product_is_sign {a b : ℤ} (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) :
    a*b=1 ∨ a*b= -1 := by
  sorry

theorem sign_twist_dot {J : Type*} [Fintype J] (u v w : J → ℤ)
    (hw : ∀ j,w j=1 ∨ w j= -1) :
    (∑ j,(u j*w j)*(v j*w j))=(∑ j,u j*v j) := by
  sorry

theorem outside_row_clears_coefficients {I J : Type*} [Fintype I] [Fintype J]
    (H : Matrix I J ℤ) (x w : J → ℤ) (b : I → ℝ)
    (hH : ∀ i j,H i j=1 ∨ H i j= -1)
    (hx : ∀ j,x j=1 ∨ x j= -1) (hw : ∀ j,w j=1 ∨ w j= -1)
    (hrep : ∀ j,(x j:ℝ)=∑ i,b i*(H i j:ℝ))
    (horth : ∀ i,(∑ j,H i j*w j)=0)
    (m : ℕ) (hm : 0<m) (hcard : Fintype.card J=4*m) :
    coefficientDenominator (orthogonalCoefficient H x)∣m := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
noncomputable section

theorem real_span_has_coefficients {I J : Type*} [Fintype I]
    (H : Matrix I J ℤ) (x : J → ℤ)
    (hx : (fun j => (x j:ℝ)) ∈ Submodule.span ℝ (Set.range (fun i j => (H i j:ℝ)))) :
    ∃ b : I → ℝ,∀ j,(x j:ℝ)=∑ i,b i*(H i j:ℝ) := by
  sorry

theorem new_sign_expansion_noncoordinate {I J : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I J ℤ) (x : J → ℤ) (a : I → ℚ)
    (hrep : ∀ j,(x j:ℚ)=∑ i,a i*(H i j:ℚ))
    (hnew : ∀ i,x≠H i ∧ x≠fun j => -H i j) : ¬IsSignedCoordinate a := by
  sorry

theorem outside_span_denominator_obstruction {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (H : Matrix I J ℤ) (x w : J → ℤ)
    (hn : 0<Fintype.card J)
    (hH : ∀ i j,H i j=1 ∨ H i j= -1)
    (hx : ∀ j,x j=1 ∨ x j= -1) (hw : ∀ j,w j=1 ∨ w j= -1)
    (hgram : ∀ i l,(∑ j,H i j*H l j)=if i=l then (Fintype.card J:ℤ) else 0)
    (hspan : (fun j => (x j:ℝ)) ∈ Submodule.span ℝ (Set.range (fun i j => (H i j:ℝ))))
    (horth : ∀ i,(∑ j,H i j*w j)=0)
    (hnew : ∀ i,x≠H i ∧ x≠fun j => -H i j)
    (m : ℕ) (hm : 0<m) (hcard : Fintype.card J=4*m) :
    1<coefficientDenominator (orthogonalCoefficient H x) ∧
    coefficientDenominator (orthogonalCoefficient H x)∣m ∧
    m.minFac≤coefficientDenominator (orthogonalCoefficient H x) := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
noncomputable section

theorem spanning_columns_have_anchor {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (H : Matrix I J ℚ)
    (hspan : Submodule.span ℚ (Set.range H.col)=⊤) :
    ∃ c : I ↪ J,(H.submatrix id c).det≠0 := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
open scoped Matrix
noncomputable section

theorem row_gram_spans_columns {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (H : Matrix I J ℚ) (n : ℚ) (hn : n≠0) (hg : H*H.transpose=n • 1) :
    Submodule.span ℚ (Set.range H.col)=⊤ := by
  sorry

theorem integral_gram_has_anchor {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (H : Matrix I J ℤ) (n : ℕ) (hn : 0<n)
    (hg : ∀ i l,(∑ j,H i j*H l j)=if i=l then (n:ℤ) else 0) :
    ∃ c : I ↪ J,(H.submatrix id c).det≠0 := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
noncomputable section
open scoped Matrix

theorem anchor_expansion_equations {I J : Type*} [Fintype I]
    (H : Matrix I J ℤ) (x : J → ℤ) (a : I → ℚ)
    (hrep : ∀ j,(x j:ℚ)=∑ i,a i*(H i j:ℚ)) (c : I → J) :
    (fun i l => ((H.submatrix id c).transpose i l:ℚ))*ᵥa=fun i => (x (c i):ℚ) := by
  sorry

theorem outside_span_sharp_denominator_bound {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (H : Matrix I J ℤ) (x w : J → ℤ)
    (hn : 0<Fintype.card J)
    (hH : ∀ i j,H i j=1 ∨ H i j= -1)
    (hx : ∀ j,x j=1 ∨ x j= -1) (hw : ∀ j,w j=1 ∨ w j= -1)
    (hgram : ∀ i l,(∑ j,H i j*H l j)=if i=l then (Fintype.card J:ℤ) else 0)
    (hspan : (fun j => (x j:ℝ)) ∈ Submodule.span ℝ (Set.range (fun i j => (H i j:ℝ))))
    (horth : ∀ i,(∑ j,H i j*w j)=0)
    (hnew : ∀ i,x≠H i ∧ x≠fun j => -H i j)
    (m : ℕ) (hm : 0<m) (hodd : Odd m) (hcard : Fintype.card J=4*m) :
    (m.minFac:ℝ)≤(Fintype.card I:ℝ)^((Fintype.card I:ℝ)/2)/(2:ℝ)^(Fintype.card I-1) ∧
    1<coefficientDenominator (orthogonalCoefficient H x) ∧
    coefficientDenominator (orthogonalCoefficient H x)∣m ∧
    (∀ c : I ↪ J,(coefficientDenominator (orthogonalCoefficient H x):ℤ)∣
      (H.submatrix id c).det/(2:ℤ)^(Fintype.card I-1)) := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
noncomputable section

theorem integral_hadamard_entries_sign {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (i j : J) : A i j=1 ∨ A i j= -1 := by
  sorry

theorem integral_hadamard_row_gram {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (i l : J) :
    (∑ j,A i j*A l j)=if i=l then (Fintype.card J:ℤ) else 0 := by
  sorry

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
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
noncomputable section
open scoped Matrix

theorem retained_orthogonality_forces_deleted_span {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (hn : 0<Fintype.card J)
    (S : Finset J) (x : J → ℤ)
    (horth : ∀ i,i∉S → (∑ j,x j*A i j)=0) :
    (fun j => (x j:ℝ)) ∈ Submodule.span ℝ (Set.range (fun i : S => fun j => (A i j:ℝ))) := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
noncomputable section

/-- A reduced observation trade written in normalized sign coordinates.
The final two fields preserve precisely the moments of degrees one and two. -/
def IsReducedNormalizedObservationTrade {J : Type*} [Fintype J]
    (A B : Matrix J J ℤ) (c₀ : J) (S : Finset J) : Prop :=
  (∀ r,A r c₀=1) ∧ (∀ r,B r c₀=1) ∧
  (∀ r c,B r c=1 ∨ B r c= -1) ∧
  (∀ r,r∉S → B r=A r) ∧
  (∀ r,r∈S → ∀ t,t∈S → B r≠A t) ∧
  (∀ c,c≠c₀ → (∑ r,B r c)=(∑ r,A r c)) ∧
  (∀ c d,c≠c₀ → d≠c₀ → (∑ r,B r c*B r d)=(∑ r,A r c*A r d))

theorem normalized_moments_preserve_column_gram {J : Type*} [Fintype J]
    [DecidableEq J] (A B : Matrix J J ℤ) (c₀ : J)
    (hA : ∀ r,A r c₀=1) (hB : ∀ r,B r c₀=1)
    (hfirst : ∀ c,c≠c₀ → (∑ r,B r c)=(∑ r,A r c))
    (hsecond : ∀ c d,c≠c₀ → d≠c₀ → (∑ r,B r c*B r d)=(∑ r,A r c*A r d)) :
    B.transpose*B=A.transpose*A := by
  sorry

theorem reduced_observation_trade_is_hadamard {J : Type*} [Fintype J] [DecidableEq J]
    (A B : Matrix J J ℤ) (hA : A.IsHadamard) (hn : 0<Fintype.card J)
    (c₀ : J) (S : Finset J) (ht : IsReducedNormalizedObservationTrade A B c₀ S) :
    B.IsHadamard := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
noncomputable section

theorem reduced_trade_prime_factor_volume_bound {J : Type*} [Fintype J] [DecidableEq J]
    (A B : Matrix J J ℤ) (hA : A.IsHadamard) (c₀ : J) (S : Finset J)
    (ht : IsReducedNormalizedObservationTrade A B c₀ S)
    (hS : S.Nonempty) (hr : S.card<Fintype.card J)
    (m : ℕ) (hm : 1<m) (hodd : Odd m) (hcard : Fintype.card J=4*m) :
    (m.minFac:ℝ)≤(S.card:ℝ)^((S.card:ℝ)/2)/(2:ℝ)^(S.card-1) := by
  sorry

theorem no_reduced_trade_below_determinant_threshold {J : Type*} [Fintype J] [DecidableEq J]
    (A B : Matrix J J ℤ) (hA : A.IsHadamard) (c₀ : J) (S : Finset J)
    (ht : IsReducedNormalizedObservationTrade A B c₀ S)
    (m R : ℕ) (hm : 1<m) (hodd : Odd m) (hcard : Fintype.card J=4*m)
    (hR : R<Fintype.card J) (hdegree : S.card≤R)
    (hbound : ∀ r : ℕ,1≤r → r≤R →
      (r:ℝ)^((r:ℝ)/2)/(2:ℝ)^(r-1)<(m.minFac:ℝ)) : S=∅ := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.DenominatorTrades
noncomputable section

theorem normalized_determinant_envelope_at_four_mul (m : ℕ) (hm : 0<m) :
    (m:ℝ)≤((4*m:ℕ):ℝ)^(((4*m:ℕ):ℝ)/2)/(2:ℝ)^(4*m-1) := by
  sorry

theorem determinant_threshold_forces_degree_lt_order (m R : ℕ) (hm : 0<m)
    (hbound : ∀ r : ℕ,1≤r → r≤R →
      (r:ℝ)^((r:ℝ)/2)/(2:ℝ)^(r-1)<(m.minFac:ℝ)) : R<4*m := by
  sorry

theorem bounded_degree_observation_trades_are_isolated {J : Type*} [Fintype J] [DecidableEq J]
    (A B : Matrix J J ℤ) (hA : A.IsHadamard) (c₀ : J) (S : Finset J)
    (ht : IsReducedNormalizedObservationTrade A B c₀ S)
    (m R : ℕ) (hm : 1<m) (hodd : Odd m) (hcard : Fintype.card J=4*m)
    (hdegree : S.card≤R)
    (hbound : ∀ r : ℕ,1≤r → r≤R →
      (r:ℝ)^((r:ℝ)/2)/(2:ℝ)^(r-1)<(m.minFac:ℝ)) : S=∅ := by
  sorry

end
end EntropyDesigns.DenominatorTrades


namespace EntropyDesigns.PrimeExponentRigidity

theorem prime_divisor_of_three_prime_power_successor (k l : ℕ)
    (hk : k.Prime) (hko : Odd k) (hl : l.Prime) (hl2 : l≠2)
    (hd : l∣3^k+1) : 2*k∣l-1 := by
  sorry

end EntropyDesigns.PrimeExponentRigidity


namespace EntropyDesigns.PrimeExponentRigidity
noncomputable section

def primePowerOrder (k : ℕ) : ℕ := 3^k+1

def primePowerOddParameter (k : ℕ) : ℕ := (3^k+1)/4

theorem paley_prime_exponent_order (k : ℕ) (hko : Odd k) :
    ∃ A : Matrix (Fin (primePowerOrder k)) (Fin (primePowerOrder k)) ℤ,A.IsHadamard := by
  sorry

theorem prime_power_parameter_properties (k : ℕ) (hk : k.Prime) (hko : Odd k) :
    4*primePowerOddParameter k=primePowerOrder k ∧ Odd (primePowerOddParameter k) ∧
    1<primePowerOddParameter k ∧ (primePowerOrder k)%8=4 := by
  sorry

theorem prime_power_parameter_roughness (k : ℕ) (hk : k.Prime) (hko : Odd k) :
    2*k+1≤(primePowerOddParameter k).minFac := by
  sorry

end
end EntropyDesigns.PrimeExponentRigidity


namespace EntropyDesigns.PrimeExponentRigidity
noncomputable section

def determinantEnvelope (d : ℕ) : ℝ := (d:ℝ)^((d:ℝ)/2)/(2:ℝ)^(d-1)

theorem determinant_envelope_below_log_threshold (p s epsilon : ℝ)
    (hp : 0<p) (hs : 0<s) (hepsilon : 0<epsilon) (hlogs : 2<Real.log s)
    (hlower : (1-epsilon/4)*s≤Real.log p)
    (d : ℕ) (hd : 1≤d) (hdegree : (d:ℝ)≤(2-epsilon)*s/Real.log s) :
    determinantEnvelope d<p := by
  sorry

theorem determinant_envelope_le_integer_bound (R d : ℕ) (hd : 1≤d) (hdR : d≤R) :
    determinantEnvelope d≤(((R+1)^(R+1):ℕ):ℝ) := by
  sorry

end
end EntropyDesigns.PrimeExponentRigidity


namespace EntropyDesigns.PrimeExponentRigidity
noncomputable section

/-- Every normalized sign-coordinate observation fiber at this order is
isolated under reduced degree-two-moment-preserving moves of degree at most R. -/
def IsRigidOrderAtDegree (n R : ℕ) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) ℤ,∀ c₀ : Fin n,∀ S : Finset (Fin n),
    A.IsHadamard → DenominatorTrades.IsReducedNormalizedObservationTrade A B c₀ S →
    S.card≤R → S=∅

theorem exponent_lt_prime_power_order (k : ℕ) : k<primePowerOrder k := by
  sorry

theorem prime_exponent_rigid_above_bound (k R : ℕ) (hk : k.Prime) (hko : Odd k)
    (hlarge : (R+1)^(R+1)<k) : IsRigidOrderAtDegree (primePowerOrder k) R := by
  sorry

theorem unbounded_known_rigid_orders (R N : ℕ) :
    ∃ n : ℕ,N<n ∧ n%8=4 ∧
      (∃ A : Matrix (Fin n) (Fin n) ℤ,A.IsHadamard) ∧ IsRigidOrderAtDegree n R := by
  sorry

theorem infinitely_many_known_rigid_orders (R : ℕ) :
    Set.Infinite {n : ℕ | n%8=4 ∧
      (∃ A : Matrix (Fin n) (Fin n) ℤ,A.IsHadamard) ∧ IsRigidOrderAtDegree n R} := by
  sorry

end
end EntropyDesigns.PrimeExponentRigidity


namespace EntropyDesigns.PrimeExponentRigidity
noncomputable section
open Filter

def orderLogLog (k : ℕ) : ℝ := Real.log (Real.log (primePowerOrder k:ℝ))

theorem prime_power_order_log_upper (k : ℕ) (hk : 1≤k) :
    Real.log (primePowerOrder k:ℝ)≤2*(k:ℝ)*Real.log 3 := by
  sorry

theorem prime_parameter_log_lower (k : ℕ) (hk : k.Prime) (hko : Odd k) :
    orderLogLog k-abs (Real.log (Real.log 3))≤
      Real.log ((primePowerOddParameter k).minFac:ℝ) := by
  sorry

theorem prime_power_order_tendsto :
    Tendsto (fun k : ℕ => (primePowerOrder k:ℝ)) atTop atTop := by
  sorry

theorem order_loglog_tendsto : Tendsto orderLogLog atTop atTop := by
  sorry

theorem eventual_log_threshold_inputs (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ K : ℕ,∀ k : ℕ,K≤k → k.Prime → Odd k →
      0<orderLogLog k ∧ 2<Real.log (orderLogLog k) ∧
      (1-epsilon/4)*orderLogLog k≤Real.log ((primePowerOddParameter k).minFac:ℝ) := by
  sorry

end
end EntropyDesigns.PrimeExponentRigidity


namespace EntropyDesigns.PrimeExponentRigidity
noncomputable section

theorem prime_exponent_quantitative_trade_bound (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ K : ℕ,∀ k : ℕ,K≤k → k.Prime → Odd k →
      ∀ A B : Matrix (Fin (primePowerOrder k)) (Fin (primePowerOrder k)) ℤ,
      ∀ c₀ : Fin (primePowerOrder k),∀ S : Finset (Fin (primePowerOrder k)),
      A.IsHadamard → DenominatorTrades.IsReducedNormalizedObservationTrade A B c₀ S →
      S.Nonempty → (2-epsilon)*orderLogLog k/Real.log (orderLogLog k)≤(S.card:ℝ) := by
  sorry

end
end EntropyDesigns.PrimeExponentRigidity


namespace EntropyDesigns.PrimeExponentRigidity
noncomputable section
open Filter

def selectedExponent (i : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (i+3))

def selectedOrder (i : ℕ) : ℕ := primePowerOrder (selectedExponent i)

theorem selected_exponent_properties (i : ℕ) :
    i+3≤selectedExponent i ∧ (selectedExponent i).Prime ∧ Odd (selectedExponent i) := by
  sorry

theorem selected_order_properties (i : ℕ) :
    (selectedOrder i)%8=4 ∧
      ∃ A : Matrix (Fin (selectedOrder i)) (Fin (selectedOrder i)) ℤ,A.IsHadamard := by
  sorry

theorem selected_order_tendsto : Tendsto selectedOrder atTop atTop := by
  sorry

theorem quantitative_infinite_rigidity_subsequence :
    ∃ n : ℕ → ℕ,Tendsto n atTop atTop ∧
      (∀ i,(n i)%8=4 ∧ ∃ A : Matrix (Fin (n i)) (Fin (n i)) ℤ,A.IsHadamard) ∧
      ∀ epsilon : ℝ,0<epsilon → ∀ᶠ i : ℕ in atTop,
      ∀ A B : Matrix (Fin (n i)) (Fin (n i)) ℤ,∀ c₀ : Fin (n i),∀ S : Finset (Fin (n i)),
      A.IsHadamard → DenominatorTrades.IsReducedNormalizedObservationTrade A B c₀ S →
      S.Nonempty →
      (2-epsilon)*Real.log (Real.log (n i:ℝ))/Real.log (Real.log (Real.log (n i:ℝ)))≤(S.card:ℝ) := by
  sorry

end
end EntropyDesigns.PrimeExponentRigidity
