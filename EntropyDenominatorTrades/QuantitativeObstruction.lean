/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.SpanDenominator
public import EntropyDenominatorTrades.GramAnchor
public import EntropyDenominatorTrades.IntegerAnchors
public import Mathlib.Algebra.Order.Ring.Abs
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
noncomputable section
open scoped Matrix

theorem anchor_expansion_equations {I J : Type*} [Fintype I]
    (H : Matrix I J ℤ) (x : J → ℤ) (a : I → ℚ)
    (hrep : ∀ j,(x j:ℚ)=∑ i,a i*(H i j:ℚ)) (c : I → J) :
    (fun i l => ((H.submatrix id c).transpose i l:ℚ))*ᵥa=fun i => (x (c i):ℚ) := by
  funext i
  change (∑ l,(H l (c i):ℚ)*a l)=(x (c i):ℚ)
  rw [hrep]
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

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
  classical
  obtain ⟨b,hb⟩ := real_span_has_coefficients H x hspan
  have hr := rational_expansion_of_real_representation H x b hn hgram hb
  have hu := rational_sign_coefficients_unit H x hn hx hr
  letI : Nonempty I := by
    by_contra h
    haveI : IsEmpty I := not_nonempty_iff.mp h
    simp at hu
  let pivot : I := Classical.arbitrary I
  obtain ⟨hq,hd,hp⟩ := outside_span_denominator_obstruction H x w hn hH hx hw hgram hspan horth hnew m hm hcard
  have hqo := hodd.of_dvd_nat hd
  obtain ⟨c,hc⟩ := integral_gram_has_anchor H (Fintype.card J) hn hgram
  have hs : ∀ i j,(H.submatrix id c).transpose i j=1 ∨ (H.submatrix id c).transpose i j= -1 :=
    fun i j => hH j (c i)
  have hbound := odd_anchor_denominator_bound (H.submatrix id c).transpose pivot hs
    (orthogonalCoefficient H x) (fun i => x (c i)) (anchor_expansion_equations H x _ hr c)
    hqo (by simpa only [Matrix.det_transpose] using hc)
  refine ⟨(show (m.minFac:ℝ)≤(coefficientDenominator (orthogonalCoefficient H x):ℝ) by exact_mod_cast hp).trans hbound,hq,hd,?_⟩
  intro d
  have he := odd_denominator_divides_normalized_anchor (H.submatrix id d).transpose pivot
    (fun i j => hH j (d i)) (orthogonalCoefficient H x) (fun i => x (d i))
    (anchor_expansion_equations H x _ hr d) hqo
  simpa only [Matrix.det_transpose] using he

end
end EntropyDesigns.DenominatorTrades
