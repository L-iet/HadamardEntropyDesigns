/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.OutsideBalancing
public import EntropyDenominatorTrades.UnitCoefficients
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
noncomputable section

theorem real_span_has_coefficients {I J : Type*} [Fintype I]
    (H : Matrix I J ℤ) (x : J → ℤ)
    (hx : (fun j => (x j:ℝ)) ∈ Submodule.span ℝ (Set.range (fun i j => (H i j:ℝ)))) :
    ∃ b : I → ℝ,∀ j,(x j:ℝ)=∑ i,b i*(H i j:ℝ) := by
  obtain ⟨b,hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  refine ⟨b,?_⟩
  intro j
  have he := congrArg (fun f : J → ℝ => f j) hb
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using he.symm

theorem new_sign_expansion_noncoordinate {I J : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I J ℤ) (x : J → ℤ) (a : I → ℚ)
    (hrep : ∀ j,(x j:ℚ)=∑ i,a i*(H i j:ℚ))
    (hnew : ∀ i,x≠H i ∧ x≠fun j => -H i j) : ¬IsSignedCoordinate a := by
  rintro ⟨i,e,he,ha⟩
  have hx (j : J) : (x j:ℚ)=(e:ℚ)*(H i j:ℚ) := by
    rw [hrep j]
    simp only [ha,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rcases he with he|he
  · apply (hnew i).1
    funext j
    have ht := hx j
    rw [he] at ht
    norm_num at ht
    exact_mod_cast ht
  · apply (hnew i).2
    funext j
    have ht := hx j
    rw [he] at ht
    norm_num at ht
    exact_mod_cast ht

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
  obtain ⟨b,hb⟩ := real_span_has_coefficients H x hspan
  have hr := rational_expansion_of_real_representation H x b hn hgram hb
  have hu := rational_sign_coefficients_unit H x hn hx hr
  have hq := noncoordinate_unit_denominator_gt_one _ hu
    (new_sign_expansion_noncoordinate H x _ hr hnew)
  have hd := outside_row_clears_coefficients H x w b hH hx hw hb horth m hm hcard
  exact ⟨hq,hd,Nat.minFac_le_of_dvd hq hd⟩

end
end EntropyDesigns.DenominatorTrades
