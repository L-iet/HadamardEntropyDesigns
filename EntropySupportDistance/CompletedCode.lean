/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.NormalizedOffsets
public import EntropySupportDistance.SourceRowBridge
public import EntropySupportDistance.SourceOrthogonality
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

def completedCode {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Matrix (Fin k) (Fin k) ℤ) (t : Fin k) (a : Fin s → Bool) :
    SourceOutcome k s i0 := fun z => decide
      (completedOffsetRow e i0 c (fun i j => K i j) t a ((fullColumnEquiv i0).symm (some z))= -1)

theorem completedCode_sign {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (t : Fin k) (a : Fin s → Bool) (z : SourceCoordinate k s i0) :
    bitSign (completedCode e i0 c K t a z)=
      completedOffsetRow e i0 c (fun i j => K i j) t a ((fullColumnEquiv i0).symm (some z)) := by
  classical
  let w := (fullColumnEquiv i0).symm (some z)
  have ht := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hK.apply_mem t w.1)
  have hsource := fullSourceRow_sign e i0 (offsetSeed c a) w
  change bitSign (decide (K t w.1*fullSourceRow e i0 (offsetSeed c a) w= -1))=_
  change _=K t w.1*fullSourceRow e i0 (offsetSeed c a) w
  rcases ht with h|h <;> rcases hsource with h'|h' <;> norm_num [h,h',bitSign]

theorem completedCode_first_row {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Matrix (Fin k) (Fin k) ℤ)
    (hfirst : ∀ j,K i0 j=1) (a : Fin s → Bool) :
    completedCode e i0 c K i0 a=sourceCode e i0 (offsetSeed c a) := by
  classical
  funext z
  unfold completedCode
  simp only [completedOffsetRow,hfirst,one_mul]
  rw [fullSourceRow_column_bridge]
  cases h : sourceCode e i0 (offsetSeed c a) z <;> simp [h,bitSign]

theorem completedCode_equality_implies_rows {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c d : BlockSeeds k s) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hcol : ∀ t,K t i0=1) (t u : Fin k) (a b : Fin s → Bool)
    (hcode : completedCode e i0 c K t a=completedCode e i0 d K u b) :
    completedOffsetRow e i0 c (fun i j => K i j) t a=
      completedOffsetRow e i0 d (fun i j => K i j) u b := by
  funext z
  obtain ⟨v,rfl⟩ := (fullColumnEquiv i0).symm.surjective z
  rcases v with _|v
  · change completedOffsetRow e i0 c (fun i j => K i j) t a (i0,∅)=
      completedOffsetRow e i0 d (fun i j => K i j) u b (i0,∅)
    rw [completedOffsetRow_constant_column e i0 c K hcol,
      completedOffsetRow_constant_column e i0 d K hcol]
  · rw [←completedCode_sign e i0 c K hK,←completedCode_sign e i0 d K hK,hcode]

theorem normalized_completed_codes_injective {k s : ℕ} (hs : 2≤s)
    (e : Finset (Fin s)) (i0 : Fin k) (K : Matrix (Fin k) (Fin k) ℤ)
    (hK : Matrix.IsHadamard K) (hcol : ∀ t,K t i0=1) : Function.Injective
      (fun p : OffsetParameters k s i0 × (Fin k × (Fin s → Bool)) =>
        completedCode e i0 (extendOffsets i0 p.1) K p.2.1 p.2.2) := by
  intro p q heq
  apply normalized_completed_rows_injective hs e i0 K hK
  exact completedCode_equality_implies_rows e i0 _ _ K hK hcol _ _ _ _ heq

theorem completedCode_inner_bridge {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hcol : ∀ t,K t i0=1) (t u : Fin k) (a b : Fin s → Bool) :
    (∑ j : Fin k,∑ S : Finset (Fin s),
      completedOffsetRow e i0 c (fun i j => K i j) t a (j,S)*
        completedOffsetRow e i0 c (fun i j => K i j) u b (j,S))=
      1+(∑ z : SourceCoordinate k s i0,
        bitSign (completedCode e i0 c K t a z)*bitSign (completedCode e i0 c K u b z)) := by
  classical
  have he := Equiv.sum_comp (fullColumnEquiv i0).symm
    (fun z : Fin k × Finset (Fin s) =>
      completedOffsetRow e i0 c (fun i j => K i j) t a z*
        completedOffsetRow e i0 c (fun i j => K i j) u b z)
  rw [Fintype.sum_prod_type] at he
  rw [←he,Fintype.sum_option]
  change completedOffsetRow e i0 c (fun i j => K i j) t a (i0,∅)*
    completedOffsetRow e i0 c (fun i j => K i j) u b (i0,∅)+_= _
  rw [completedOffsetRow_constant_column e i0 c K hcol,
    completedOffsetRow_constant_column e i0 c K hcol]
  simp only [mul_one,←completedCode_sign e i0 c K hK]

theorem completedCodes_orthogonal {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hcol : ∀ t,K t i0=1) (r v : Fin k × (Fin s → Bool)) (hne : r≠v) :
    observedOrthogonal (completedCode e i0 c K r.1 r.2) (completedCode e i0 c K v.1 v.2) := by
  classical
  change 1+(∑ z,bitSign (completedCode e i0 c K r.1 r.2 z)*
    bitSign (completedCode e i0 c K v.1 v.2 z))=0
  rw [←completedCode_inner_bridge e i0 c K hK hcol]
  rw [completedOffsetRow_inner]
  have hdot := congrArg (fun M : Matrix (Fin k) (Fin k) ℤ => M r.1 v.1) hK.mul_conjTranspose
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,Matrix.smul_apply,
    Matrix.one_apply,Fintype.card_fin,smul_eq_mul] at hdot
  rw [hdot]
  by_cases ha : r.2=v.2 <;> by_cases ht : r.1=v.1 <;>
    simp_all [Prod.ext_iff]

end
end EntropyDesigns.SupportFace
