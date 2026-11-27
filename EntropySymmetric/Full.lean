/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySymmetric.OrbitEntropy
public import EntropySymmetric.BinomialMode
public import EntropySymmetric.BinaryEntropyQuadratic
@[expose] public section
namespace EntropyDesigns.SymmetricEntropy
noncomputable section
open scoped BigOperators

theorem symmetric_pairwise_shannon_lower {d : ℕ} (hd : 2≤d)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hsym : CoordinatePermutationInvariant w)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    ((d:ℝ)-1)*Real.log 2-Real.log ((d:ℝ)+1)≤shannon w := by
  classical
  have hdR : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  obtain ⟨h1,h2⟩ := hamming_moments w hmass hmean hpair
  have hweight (x : Fin d → Bool) : hammingWeight x≤d := by
    unfold hammingWeight
    simpa using Finset.card_le_card (Finset.filter_subset (fun i : Fin d => x i=true) Finset.univ)
  have hpoint (x : Fin d → Bool) :
      (4*Real.log 2/(d:ℝ))*((d:ℝ)*(hammingWeight x:ℝ)-(hammingWeight x:ℝ)^2)-
        Real.log ((d:ℝ)+1)≤Real.log (Nat.choose d (hammingWeight x):ℝ) := by
    have hk : (hammingWeight x:ℝ)≤d := by exact_mod_cast hweight x
    have hp : 0≤(hammingWeight x:ℝ)/d := div_nonneg (Nat.cast_nonneg _) hdR.le
    have hp1 : (hammingWeight x:ℝ)/d≤1 := (div_le_one hdR).mpr hk
    have hb := mul_le_mul_of_nonneg_left
      (binary_entropy_quadratic_lower ((hammingWeight x:ℝ)/d) hp hp1) hdR.le
    have he : (d:ℝ)*(4*Real.log 2*((hammingWeight x:ℝ)/d)*(1-(hammingWeight x:ℝ)/d))=
        (4*Real.log 2/(d:ℝ))*((d:ℝ)*(hammingWeight x:ℝ)-(hammingWeight x:ℝ)^2) := by
      field_simp
      <;> ring
    rw [he] at hb
    have hc := log_choose_entropy (hweight x)
    linarith
  have hsum := Finset.sum_le_sum (s:=Finset.univ)
    (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw x))
  have he (x : Fin d → Bool) :
      w x*((4*Real.log 2/(d:ℝ))*((d:ℝ)*(hammingWeight x:ℝ)-(hammingWeight x:ℝ)^2)-Real.log ((d:ℝ)+1))=
      (4*Real.log 2/(d:ℝ))*((d:ℝ)*(w x*(hammingWeight x:ℝ))-w x*(hammingWeight x:ℝ)^2)-
        Real.log ((d:ℝ)+1)*w x := by ring
  simp_rw [he] at hsum
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,
    Finset.sum_sub_distrib,←Finset.mul_sum,h1,h2,hmass] at hsum
  have hleft : (4*Real.log 2/(d:ℝ))*((d:ℝ)*((d:ℝ)/2)-(d:ℝ)*((d:ℝ)+1)/4)-
      Real.log ((d:ℝ)+1)*1=((d:ℝ)-1)*Real.log 2-Real.log ((d:ℝ)+1) := by
    field_simp
    <;> ring
  rw [hleft] at hsum
  exact hsum.trans (symmetric_shannon_slice_lower w hw hmass hsym)

end
end EntropyDesigns.SymmetricEntropy
