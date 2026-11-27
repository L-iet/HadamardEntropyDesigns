/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantitative.Correlation
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

def correlatedPairs {ι : Type*} [Fintype ι] {m : ℕ} (rows : ι → Fin m → Bool) :
    Finset (Fin m × Fin m) := by
  classical
  exact Finset.univ.filter fun ij => ij.1 < ij.2 ∧ signCorrelation rows ij.1 ij.2≠0

def goodObservables {ι : Type*} [Fintype ι] {m : ℕ} (rows : ι → Fin m → Bool) :
    Finset (Fin m) := ((correlatedPairs rows).image Prod.fst)ᶜ

theorem signCorrelation_symm {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) (i j : Fin m) :
    signCorrelation rows i j=signCorrelation rows j i := by
  unfold signCorrelation
  apply Finset.sum_congr rfl
  intro z _
  exact mul_comm _ _

theorem good_observables_card {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) :
    m≤(goodObservables rows).card+(correlatedPairs rows).card := by
  classical
  have him := Finset.card_image_le (s:=correlatedPairs rows) (f:=Prod.fst)
  have hle := Finset.card_le_univ ((correlatedPairs rows).image Prod.fst)
  simp only [Fintype.card_fin] at hle
  simp only [goodObservables,Finset.card_compl,Fintype.card_fin]
  omega

theorem good_observables_uncorrelated {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) (i j : Fin m)
    (hi : i∈goodObservables rows) (hj : j∈goodObservables rows) (hne : i≠j) :
    signCorrelation rows i j=0 := by
  classical
  by_contra h
  have hnoti : i∉(correlatedPairs rows).image Prod.fst := by simpa [goodObservables] using hi
  have hnotj : j∉(correlatedPairs rows).image Prod.fst := by simpa [goodObservables] using hj
  rcases lt_or_gt_of_ne hne with hij|hji
  · apply hnoti
    apply Finset.mem_image.mpr
    exact ⟨(i,j),by simp [correlatedPairs,hij,h],rfl⟩
  · apply hnotj
    apply Finset.mem_image.mpr
    have hji0 : signCorrelation rows j i≠0 := by rwa [signCorrelation_symm rows j i]
    exact ⟨(j,i),by simp [correlatedPairs,hji,hji0],rfl⟩

theorem correlation_count_rank_tradeoff {r D m : ℕ}
    (S : Finset (Finset (Fin r))) (hres : S.card%8=4)
    (rows : S → Fin m → Bool) (hmean : ∀ i,(∑ z,bitSign (rows z i))=0)
    (f : Fin m → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r D)
    (hm : ∀ (i : Fin m) (z : S),f i z.val=if rows z i then 1 else 0) :
    m≤binaryBilinearRank (evenBinaryCode
      ((lowDegreeBooleanCode r D).map (binaryFunctionRestriction S)))+1+(correlatedPairs rows).card := by
  classical
  let G := goodObservables rows
  let e : Fin G.card ≃ G := Fintype.equivOfCardEq (by simp)
  let rowE : S → Fin G.card → Bool := fun z i => rows z (e i).val
  let fE : Fin G.card → (Finset (Fin r) → ZMod 2) := fun i => f (e i).val
  have hE : IsUniformBinaryPairwiseIndependent rowE := by
    constructor
    · intro i
      exact hmean (e i).val
    · intro i j hij
      have hne : (e i).val≠(e j).val := by
        intro h
        exact hij (e.injective (Subtype.ext h))
      exact good_observables_uncorrelated rows (e i).val (e j).val (e i).property (e j).property hne
  have hb := balanced_uncorrelated_restriction_rank S hres rowE hE fE
    (fun i => hf (e i).val) (fun i z => hm (e i).val z)
  have hc := good_observables_card rows
  change (goodObservables rows).card≤_ at hb
  omega

theorem punctured_correlation_count_lower {r : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hres : S.card%8=4) (hproper : S≠Finset.univ)
    (rows : S → Fin (S.card-4) → Bool) (hmean : ∀ i,(∑ z,bitSign (rows z i))=0)
    (f : Fin (S.card-4) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r (r-2))
    (hm : ∀ (i : Fin (S.card-4)) (z : S),f i z.val=if rows z i then 1 else 0) :
    2*(r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S)))-3≤
      (correlatedPairs rows).card := by
  let a := r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))
  let C := (lowDegreeBooleanCode r (r-2)).map (binaryFunctionRestriction S)
  let W := evenBinaryCode C
  have hd := punctured_reed_muller_radical_dimensions hr S hproper hres
  change Module.finrank (ZMod 2) C=S.card-a ∧ Module.finrank (ZMod 2) W=S.card-a-1 ∧
    Module.finrank (ZMod 2) (binaryCodeRadical W)=a+1 ∧ binaryBilinearRank W=S.card-2*a-2 at hd
  have hrad : Module.finrank (ZMod 2) (binaryCodeRadical W)≤Module.finrank (ZMod 2) W := by
    unfold binaryCodeRadical
    exact Submodule.finrank_mono inf_le_left
  rw [hd.2.2.1,hd.2.1] at hrad
  have hb := correlation_count_rank_tradeoff S hres rows hmean f hf hm
  change S.card-4≤binaryBilinearRank W+1+(correlatedPairs rows).card at hb
  rw [hd.2.2.2] at hb
  change 2*a-3≤_
  omega

end
end EntropyDesigns
