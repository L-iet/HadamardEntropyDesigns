/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupport.PuncturedRank
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

def IsUniformBinaryPairwiseIndependent {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) : Prop :=
  (∀ i,(∑ z,bitSign (rows z i))=0) ∧
    (∀ i j,i≠j → (∑ z,bitSign (rows z i)*bitSign (rows z j))=0)

theorem uniform_binary_equiv_strength_two {ι : Type*} [Fintype ι] {N m : ℕ}
    (e : Fin N ≃ ι) (rows : ι → Fin m → Bool)
    (h : IsUniformBinaryPairwiseIndependent rows) :
    IsBinaryStrengthTwo (fun j i => rows (e j) i) := by
  apply sign_moments_strength_two
  · intro i
    exact (Equiv.sum_comp e (fun z => bitSign (rows z i))).trans (h.1 i)
  · intro i j hij
    exact (Equiv.sum_comp e (fun z => bitSign (rows z i)*bitSign (rows z j))).trans (h.2 i j hij)

theorem punctured_observable_code_dimension {r D : ℕ}
    (S : Finset (Finset (Fin r))) (hN : 12≤S.card) (hres : S.card%8=4)
    (rows : S → Fin (S.card-4) → Bool) (hrows : IsUniformBinaryPairwiseIndependent rows)
    (f : Fin (S.card-4) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r D)
    (hm : ∀ (i : Fin (S.card-4)) (z : S),f i z.val=if rows z i then 1 else 0) :
    S.card-3≤Module.finrank (ZMod 2) (lowDegreeBooleanCode r D) := by
  classical
  let e : Fin S.card ≃ S := Fintype.equivOfCardEq (by simp)
  have heOA := uniform_binary_equiv_strength_two e rows hrows
  have hedim := encoded_even_binary_code_rank (N:=S.card) (r:=r) (k:=S.card-4)
    (by omega) hres (by omega) (fun j => (e j).val) (fun j i => rows (e j) i)
    heOA f hf (by intro i j; exact hm i (e j))
  omega

theorem punctured_observable_affine_codimension {r : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hN : 12≤S.card) (hres : S.card%8=4)
    (hproper : S≠Finset.univ)
    (rows : S → Fin (S.card-4) → Bool) (hrows : IsUniformBinaryPairwiseIndependent rows)
    (f : Fin (S.card-4) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r (r-2))
    (hm : ∀ (i : Fin (S.card-4)) (z : S),f i z.val=if rows z i then 1 else 0) :
    r-1≤Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S)) := by
  classical
  let e : Fin S.card ≃ S := Fintype.equivOfCardEq (by simp)
  let rowE : Fin S.card → Fin (S.card-4) → Bool := fun j i => rows (e j) i
  have hOA : IsBinaryStrengthTwo rowE := uniform_binary_equiv_strength_two e rows hrows
  let C := (lowDegreeBooleanCode r (r-2)).map (binaryFunctionRestriction S)
  let W := evenBinaryCode C
  have hW : ∀ i,(fun z : S => f i z.val)∈W := by
    intro i
    refine ⟨Submodule.mem_map.mpr ⟨f i,hf i,rfl⟩,?_⟩
    change (∑ z : S,f i z.val)=0
    rw [← Equiv.sum_comp e (fun z : S => f i z.val)]
    simp_rw [hm]
    exact binary_pairwise_column_sum (by omega) hres rowE hOA i
  let v : Fin (S.card-4) → W := fun i => ⟨fun z => f i z.val,hW i⟩
  have hgram : ∀ i j,binaryFunctionDotForm S (v i).val (v j).val=
      ((if i=j then 1 else 0) : ZMod 2)+1 := by
    intro i j
    have hg := congrFun (congrFun (general_binary_pairwise_gram (by omega) hres rowE hOA) i) j
    change (∑ z : S,f i z.val*f j z.val)=_
    rw [← Equiv.sum_comp e (fun z : S => f i z.val*f j z.val)]
    simp_rw [hm]
    simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.add_apply,Matrix.one_apply,
      allOnesMatrix,binaryObservationMatrix,rowE] using hg
  have hb := binary_even_gram_rank_bound (by omega) W v hgram
  have hd := (punctured_reed_muller_radical_dimensions hr S hproper hres).2.2.2
  change binaryBilinearRank W=_ at hd
  rw [hd] at hb
  omega

end
end EntropyDesigns
