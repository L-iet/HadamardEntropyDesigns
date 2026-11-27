/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentratedFamily.FamilyInputs
public import EntropyConcentratedFamily.PlaneLaw
public import EntropyConcentratedFamily.PartialMixture
public import EntropyConcentratedFamily.PartialRepair
public import EntropySupportDistance.RepairLower
@[expose] public section
set_option maxHeartbeats 2000000
namespace EntropyDesigns.ConcentratedFamily
noncomputable section
open SupportFace
open scoped BigOperators

theorem concentrated_sharp_distance {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) (hs : s≠0) (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    (∀ q : SourceOutcome k s i0 → ℝ,
      q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
        1-1/(k:ℝ)≤totalVariation (uniformFiniteLaw (planeSupport hs e i0 t)) q) ∧
      (∃ q : SourceOutcome k s i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
          totalVariation (uniformFiniteLaw (planeSupport hs e i0 t)) q=1-1/(k:ℝ)) := by
  classical
  have hs2 := (family_parameters hk hsize).1
  have hp := plane_uniform_feasible hk hs e he i0 t ht
  have hsupport := plane_uniform_source_supported hs e i0 t
  obtain ⟨K,hK,hfirst,hcol⟩ := normalized_walsh_exists r hkpow i0
  let F := fieldOffsetImage hs i0 t
  have hF : F.Nonempty := by
    apply Finset.card_pos.mp
    dsimp only [F]
    rw [fieldOffsetImage_card hk hs i0 t ht]
    positivity
  constructor
  · intro q hq
    exact source_all_mixtures_distance_lower e i0 hsize _ q hp.2.1 hsupport hq
  · refine ⟨partialMixture e i0 K F,partialMixture_mem hs2 e i0 K hK hcol F hF,?_⟩
    have h := partialMixture_exact_distance hs2 e i0 K hK hfirst hcol F hF
    simpa only [F,planeSupport_offset_partition] using h

theorem concentrated_exact_repair {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) (hs : s≠0) (e : Finset (Fin s)) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    ∃ K : Matrix (Fin k) (Fin k) ℤ,Matrix.IsHadamard K ∧
      (∀ j,K i0 j=1) ∧ (∀ a,K a i0=1) ∧
      ∃ G : Finset (OffsetParameters k s i0),G⊆fieldOffsetImage hs i0 t ∧ G.card=2^s/k ∧
        (selectedEndpoint e i0 K G).card=(2^s)^2 ∧
        (planeSupport hs e i0 t∩selectedEndpoint e i0 K G).card=(2^s)^2/k ∧
        (∀ c∈G,Matrix.IsHadamard (offsetHadamard e i0 (extendOffsets i0 c) K)) ∧
        selectedEndpoint e i0 K G=G.biUnion (completedBlock e i0 K) ∧
        (∃ E : {x // x∈planeSupport hs e i0 t} ≃ {y // y∈selectedEndpoint e i0 K G},
          (∀ x,(E x).val=x.val ↔ x.val∈selectedEndpoint e i0 K G) ∧
          Fintype.card {x : {x // x∈planeSupport hs e i0 t} // (E x).val≠x.val}=
            (2^s)^2-(2^s)^2/k ∧
          ((Fintype.card {x : {x // x∈planeSupport hs e i0 t} // (E x).val≠x.val}:ℕ):ℝ)=
            (((2^s)^2:ℕ):ℝ)*(1-1/(k:ℝ))) ∧
        collision (uniformFiniteLaw (planeSupport hs e i0 t))=1/((2:ℝ)^s)^2 ∧
        collision (uniformFiniteLaw (selectedEndpoint e i0 K G))=1/((2:ℝ)^s)^2 := by
  classical
  have hs2 := (family_parameters hk hsize).1
  obtain ⟨K,hK,hfirst,hcol⟩ := normalized_walsh_exists r hkpow i0
  let F := fieldOffsetImage hs i0 t
  have hF : F.Nonempty := by
    apply Finset.card_pos.mp
    dsimp only [F]
    rw [fieldOffsetImage_card hk hs i0 t ht]
    positivity
  have hdiv : k∣F.card := fieldOffsetImage_divisible hk r hkpow hsize hs i0 t ht
  have h := partial_collision_preserving_repair hs2 e i0 K hK hfirst hcol F hF hdiv
  refine ⟨K,hK,hfirst,hcol,?_⟩
  rw [planeSupport_offset_partition hs e i0 t]
  simpa only [F,fieldOffsetImage_card hk hs i0 t ht,←pow_two,Nat.cast_pow,Nat.cast_ofNat] using h

theorem concentrated_all_repairs_lower {k s b : ℕ} (hsize : 2*(k-1)<2^s) (hs : s≠0)
    (e : Finset (Fin s)) (i0 : Fin k) (t : Fin k → GaloisField 2 s)
    (x y : Fin b → Fin (k*2^s) → SourceOutcome k s i0)
    (hx : ∀ j i,x j i∈planeSupport hs e i0 t)
    (horth : ∀ j i l,i≠l → observedOrthogonal (y j i) (y j l)) :
    ((b*(k*2^s):ℕ):ℝ)*(1-1/(k:ℝ))≤
      ∑ j : Fin b,((Finset.univ.filter (fun i => x j i≠y j i)).card:ℝ) := by
  have hsub : planeSupport hs e i0 t⊆observedSupport e i0 := by
    rw [planeSupport_offset_partition]
    exact selectedOriginal_subset_source e i0 _
  exact source_all_repairs_lower e i0 hsize x y (fun j i => hsub (hx j i)) horth

end
end EntropyDesigns.ConcentratedFamily
