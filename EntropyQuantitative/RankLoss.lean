/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupport.PuncturedObservables
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

theorem binary_gram_rank_loss_at_most_one {ι : Type*} [Fintype ι] {m : ℕ}
    (W : Submodule (ZMod 2) (ι → ZMod 2)) (v : Fin m → W)
    (hgram : ∀ i j,binaryFunctionDotForm ι (v i).val (v j).val=
      ((if i=j then 1 else 0) : ZMod 2)+1) :
    m≤binaryBilinearRank W+1 := by
  by_cases he : m%2=0
  · have hb := binary_even_gram_rank_bound he W v hgram
    omega
  · have hodd : m%2=1 := by omega
    let e : Fin (m-1) ↪ Fin m :=
      ⟨Fin.castLE (Nat.sub_le m 1),by intro i j h; exact Fin.ext (congrArg (fun z : Fin m => z.val) h)⟩
    have hg : ∀ i j,binaryFunctionDotForm ι (v (e i)).val (v (e j)).val=
        ((if i=j then 1 else 0) : ZMod 2)+1 := by
      intro i j
      simpa only [e.injective.eq_iff] using hgram (e i) (e j)
    have hb := binary_even_gram_rank_bound (by omega : (m-1)%2=0) W (fun i => v (e i)) hg
    omega

theorem balanced_uncorrelated_restriction_rank {r D k : ℕ}
    (S : Finset (Finset (Fin r))) (hres : S.card%8=4)
    (rows : S → Fin k → Bool) (hrows : IsUniformBinaryPairwiseIndependent rows)
    (f : Fin k → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r D)
    (hm : ∀ (i : Fin k) (z : S),f i z.val=if rows z i then 1 else 0) :
    k≤binaryBilinearRank (evenBinaryCode
      ((lowDegreeBooleanCode r D).map (binaryFunctionRestriction S)))+1 := by
  by_cases hk : 2≤k
  ·
    classical
    let e : Fin S.card ≃ S := Fintype.equivOfCardEq (by simp)
    let rowE : Fin S.card → Fin (k) → Bool := fun j i => rows (e j) i
    have hOA : IsBinaryStrengthTwo rowE := uniform_binary_equiv_strength_two e rows hrows
    let C := (lowDegreeBooleanCode r D).map (binaryFunctionRestriction S)
    let W := evenBinaryCode C
    have hW : ∀ i,(fun z : S => f i z.val)∈W := by
      intro i
      refine ⟨Submodule.mem_map.mpr ⟨f i,hf i,rfl⟩,?_⟩
      change (∑ z : S,f i z.val)=0
      rw [← Equiv.sum_comp e (fun z : S => f i z.val)]
      simp_rw [hm]
      exact binary_pairwise_column_sum hk hres rowE hOA i
    let v : Fin (k) → W := fun i => ⟨fun z => f i z.val,hW i⟩
    have hgram : ∀ i j,binaryFunctionDotForm S (v i).val (v j).val=
        ((if i=j then 1 else 0) : ZMod 2)+1 := by
      intro i j
      have hg := congrFun (congrFun (general_binary_pairwise_gram hk hres rowE hOA) i) j
      change (∑ z : S,f i z.val*f j z.val)=_
      rw [← Equiv.sum_comp e (fun z : S => f i z.val*f j z.val)]
      simp_rw [hm]
      simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.add_apply,Matrix.one_apply,
        allOnesMatrix,binaryObservationMatrix,rowE] using hg
    exact binary_gram_rank_loss_at_most_one W v hgram
  · omega

end
end EntropyDesigns
