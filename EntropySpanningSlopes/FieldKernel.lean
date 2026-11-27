/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySpanningSlopes.FieldPairCounts
public import EntropySupportDistance.SourceOrthogonality
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace EntropyDesigns.SpanningSlopes
noncomputable section
open SupportFace
open scoped BigOperators

def negativeSlopeIndices {k s : ℕ} (hs : s≠0) (e : Finset (Fin s)) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (p q : GaloisField 2 s × GaloisField 2 s) : Finset (Fin k) :=
  Finset.univ.filter (fun j => maskFieldFunctional hs e ((t j-t i0)*(p.2-q.2))=1)

theorem binarySign_indicator (z : ZMod 2) :
    binarySign z=1-2*(if z=1 then (1:ℝ) else 0) := by
  rcases binaryField_cases z with hz|hz <;> norm_num [binarySign,hz]

theorem field_kernel_real_formula {k s : ℕ} (hs : s≠0) (e : Finset (Fin s)) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (p q : GaloisField 2 s × GaloisField 2 s) :
    ((fullSourceInner e i0 (fieldSlopeSeeds hs t p) (fieldSlopeSeeds hs t q):ℤ):ℝ)=
      (2:ℝ)^s*((equalSeedIndices hs t p q).card:ℝ)-
        2*((negativeSlopeIndices hs e i0 t p q).card:ℝ) := by
  classical
  have hi := fullSourceInner_formula e i0 (fieldSlopeSeeds hs t p) (fieldSlopeSeeds hs t q)
  rw [equalSeedIndices_sum] at hi
  have hr : ((fullSourceInner e i0 (fieldSlopeSeeds hs t p) (fieldSlopeSeeds hs t q):ℤ):ℝ)=
      (2:ℝ)^s*((equalSeedIndices hs t p q).card:ℝ)-(k:ℝ)+
        ∑ j : Fin k,((relativeChar e (fieldSlopeSeeds hs t p) (fieldSlopeSeeds hs t q) i0*
          relativeChar e (fieldSlopeSeeds hs t p) (fieldSlopeSeeds hs t q) j:ℤ):ℝ) := by
    exact_mod_cast hi
  have hc : (∑ j : Fin k,if maskFieldFunctional hs e ((t j-t i0)*(p.2-q.2))=1 then (1:ℝ) else 0)=
      ((negativeSlopeIndices hs e i0 t p q).card:ℝ) := by
    rw [←Finset.sum_filter]
    simp [negativeSlopeIndices]
  have hsum : (∑ j : Fin k,((relativeChar e (fieldSlopeSeeds hs t p) (fieldSlopeSeeds hs t q) i0*
      relativeChar e (fieldSlopeSeeds hs t p) (fieldSlopeSeeds hs t q) j:ℤ):ℝ))=
      (k:ℝ)-2*((negativeSlopeIndices hs e i0 t p q).card:ℝ) := by
    simp_rw [field_mixed_relative_character,binarySign_indicator]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      ←Finset.mul_sum,hc]
  rw [hr,hsum]
  ring

theorem field_pair_nonorthogonal_of_negative_window {k s : ℕ} (hs : s≠0)
    (e : Finset (Fin s)) (i0 : Fin k) (t : Fin k → GaloisField 2 s) (ht : Function.Injective t)
    (p q : GaloisField 2 s × GaloisField 2 s) (hb : p.2-q.2≠0)
    (hlo : 0<(negativeSlopeIndices hs e i0 t p q).card)
    (hhi : 2*(negativeSlopeIndices hs e i0 t p q).card<2^s) :
    ¬observedOrthogonal (sourceCode e i0 (fieldSlopeSeeds hs t p))
      (sourceCode e i0 (fieldSlopeSeeds hs t q)) := by
  intro horth
  have hz := (observed_orthogonal_iff e i0 (fieldSlopeSeeds hs t p) (fieldSlopeSeeds hs t q)).mp horth
  have hzreal : ((fullSourceInner e i0 (fieldSlopeSeeds hs t p) (fieldSlopeSeeds hs t q):ℤ):ℝ)=0 := by
    exact_mod_cast hz
  have hkernel := field_kernel_real_formula hs e i0 t p q
  have hc := unequal_second_seed_at_most_one hs t ht p q hb
  have hcCases : (equalSeedIndices hs t p q).card=0 ∨ (equalSeedIndices hs t p q).card=1 := by omega
  have hdpos : (0:ℝ)<(negativeSlopeIndices hs e i0 t p q).card := by exact_mod_cast hlo
  have hdhi : (2:ℝ)*((negativeSlopeIndices hs e i0 t p q).card:ℝ)<(2:ℝ)^s := by exact_mod_cast hhi
  rcases hcCases with hc0|hc1
  · rw [hc0] at hkernel
    simp only [Nat.cast_zero,mul_zero] at hkernel
    linarith
  · rw [hc1] at hkernel
    simp only [Nat.cast_one,mul_one] at hkernel
    linarith

theorem same_second_field_pair_orthogonal {k s : ℕ} (hs : s≠0)
    (e : Finset (Fin s)) (i0 : Fin k) (t : Fin k → GaloisField 2 s)
    (p q : GaloisField 2 s × GaloisField 2 s) (hb : p.2=q.2) (hpq : p≠q) :
    observedOrthogonal (sourceCode e i0 (fieldSlopeSeeds hs t p))
      (sourceCode e i0 (fieldSlopeSeeds hs t q)) := by
  classical
  have heq := equal_second_seed_no_equal_blocks hs t p q hb hpq
  have hneg : negativeSlopeIndices hs e i0 t p q=∅ := by
    ext j
    simp [negativeSlopeIndices,hb]
  apply (observed_orthogonal_iff e i0 (fieldSlopeSeeds hs t p) (fieldSlopeSeeds hs t q)).mpr
  have hr := field_kernel_real_formula hs e i0 t p q
  rw [heq,hneg] at hr
  simp only [Finset.card_empty,Nat.cast_zero,mul_zero,sub_zero] at hr
  exact_mod_cast hr

end
end EntropyDesigns.SpanningSlopes
