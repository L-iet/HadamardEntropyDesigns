/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.EvenRestriction
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators Matrix

def integerHadamardTruthRows {d : ℕ} (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) :
    Fin (d+1) → Fin d → Bool := fun r i => decide (H r i.succ= -1)

theorem integerHadamardTruthRows_value {d : ℕ}
    {H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ} (hH : Matrix.IsHadamard H)
    (r : Fin (d+1)) (i : Fin d) : bitSign (integerHadamardTruthRows H r i)=H r i.succ := by
  have hs : H r i.succ=1 ∨ H r i.succ= -1 :=
    Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem r i.succ)
  rcases hs with hs|hs <;> norm_num [integerHadamardTruthRows,bitSign,hs]

theorem integerHadamardTruthRows_strength_two {d : ℕ}
    {H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ} (hH : Matrix.IsHadamard H)
    (hzero : ∀ r,H r 0=1) : IsBinaryStrengthTwo (integerHadamardTruthRows H) := by
  apply sign_moments_strength_two
  · intro i
    simp_rw [integerHadamardTruthRows_value hH]
    have hne : (0 : Fin (d+1))≠i.succ := Ne.symm (Fin.succ_ne_zero i)
    have hc := congrArg (fun M => M 0 i.succ) hH.conjTranspose_mul
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,hne,ite_false,mul_zero,hzero,one_mul] using hc
  · intro i j hij
    simp_rw [integerHadamardTruthRows_value hH]
    have hne : i.succ≠j.succ := by
      intro h
      apply hij
      apply Fin.ext
      have hh := congrArg (fun k : Fin (d+1) => k.val) h
      simp only [Fin.val_succ] at hh
      omega
    have hc := congrArg (fun M => M i.succ j.succ) hH.conjTranspose_mul
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,hne,ite_false,mul_zero] using hc

theorem booleanValueSign_injective : Function.Injective booleanValueSign := by decide

theorem integerHadamardTruthRows_binary_value {d : ℕ}
    {H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ} (hH : Matrix.IsHadamard H)
    (r : Fin (d+1)) (i : Fin d) :
    booleanValueSign (binaryObservationMatrix (integerHadamardTruthRows H) r i)=H r i.succ := by
  have hh := integerHadamardTruthRows_value hH r i
  cases hb : integerHadamardTruthRows H r i <;>
    simpa [binaryObservationMatrix,booleanValueSign,bitSign,hb] using hh

theorem binary_strength_two_restrict {N m k : ℕ} (rows : Fin N → Fin m → Bool)
    (hOA : IsBinaryStrengthTwo rows) (e : Fin k ↪ Fin m) :
    IsBinaryStrengthTwo (fun r i => rows r (e i)) := by
  intro i j hij a b
  exact hOA (e i) (e j) (fun h => hij (e.injective h)) a b

def NoQuadraticHadamardSeedEncoding (d r : ℕ) : Prop :=
  ∀ H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ,Matrix.IsHadamard H → (∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1) →
  ∀ labels : Fin (d+1) → Finset (Fin r),Function.Injective labels →
  ∀ f : Fin d → (Finset (Fin r) → ZMod 2),
    (∀ j i,booleanValueSign (f i (labels j))=H j i.succ) →
    ¬(∀ i,f i∈lowDegreeBooleanCode r 2)

theorem order_twelve_no_quadratic_hadamard_seed : NoQuadraticHadamardSeedEncoding 11 4 := by
  intro H hH hzero labels hinj f hmatch hf
  let e : Fin 10 ↪ Fin 11 := ⟨Fin.castLE (by decide),by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 11 => k.val) h)⟩
  let rows := integerHadamardTruthRows H
  have hOA := binary_strength_two_restrict rows (integerHadamardTruthRows_strength_two hH hzero) e
  apply order_twelve_quadratic_encoding_impossible labels hinj (fun r i => rows r (e i)) hOA
    (fun i => f (e i)) (fun i => hf (e i))
  intro i j
  apply booleanValueSign_injective
  exact (hmatch j (e i)).trans (integerHadamardTruthRows_binary_value hH j (e i)).symm

theorem order_twenty_no_quadratic_hadamard_seed : NoQuadraticHadamardSeedEncoding 19 5 := by
  intro H hH hzero labels hinj f hmatch hf
  let e : Fin 18 ↪ Fin 19 := ⟨Fin.castLE (by decide),by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 19 => k.val) h)⟩
  let rows := integerHadamardTruthRows H
  have hOA := binary_strength_two_restrict rows (integerHadamardTruthRows_strength_two hH hzero) e
  have hvalues : ∀ i j,f (e i) (labels j)=
      binaryObservationMatrix (fun r i => rows r (e i)) j i := by
    intro i j
    apply booleanValueSign_injective
    exact (hmatch j (e i)).trans (integerHadamardTruthRows_binary_value hH j (e i)).symm
  have hh := encoded_binary_pairwise_degree_lower (N:=20) (r:=5) (d:=2)
    (by omega) (by decide) (by decide) (by decide) labels
    (fun r i => rows r (e i)) hOA (fun i => f (e i)) (fun i => hf (e i)) hvalues
  omega

end
end EntropyDesigns
