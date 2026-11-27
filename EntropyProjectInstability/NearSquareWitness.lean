/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyProjectInstability.FamilyIdentities
@[expose] public section
namespace EntropyDesigns.ProjectInstability
open Filter Asymptotics RelativeSequence GapTransfer SupportFace
open scoped Topology
noncomputable section

/-- Full unconditional near-square instability. The power exponents are
specified by logarithmic limits, the TV remainder by its normalized limit,
and ALL positive-order Renyi and min-entropy conclusions use the SAME laws.
The concrete complete-law data includes exact isotropy, uniformity, vertex
and strict local optimality, and an actual attained global optimizer. -/
theorem unconditional_near_square_instability :
    ∃ F : DyadicLawFamily,
      (∀ i,knownHadamardOrder (F.lowOrder i) ∧ knownHadamardOrder (F.fullOrder i) ∧
        (Concentration.observedAtoms (F.D i).law).card=(F.seedOrder i)^2 ∧
        collision (F.D i).law=1/(F.seedOrder i:ℝ)^2 ∧
        collision (F.D i).optimizer=1/(F.fullOrder i:ℝ)) ∧
      Tendsto (fun i => (F.fullOrder i:ℝ)) atTop atTop ∧
      Tendsto (fun i => collision (F.D i).law/collision (F.D i).optimizer) atTop (nhds 1) ∧
      Tendsto (fun i => Real.log (1-collision (F.D i).law/collision (F.D i).optimizer)/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(1:ℝ)/2)) ∧
      Tendsto (fun i => Real.log (collision (F.D i).optimizer-collision (F.D i).law)/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(3:ℝ)/2)) ∧
      Tendsto (fun i => Real.log (((Concentration.observedAtoms (F.D i).law).card:ℝ)-(F.fullOrder i:ℝ))/Real.log ((F.fullOrder i:ℝ))) atTop (nhds ((1:ℝ)/2)) ∧
      (∀ α : ℝ,0<α → Tendsto (fun i => Real.log (renyiEntropy (F.D i).law α-renyiEntropy (F.D i).optimizer α)/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(1:ℝ)/2))) ∧
      Tendsto (fun i => Real.log (minEntropy (F.D i).law-minEntropy (F.D i).optimizer)/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(1:ℝ)/2)) ∧
      Tendsto (fun i => Real.sqrt ((F.fullOrder i:ℝ))/(F.lowOrder i:ℝ)) atTop (nhds 1) ∧
      Tendsto (fun i => 1-1/(F.lowOrder i:ℝ)) atTop (nhds 1) ∧
      (∀ i,∀ q : SourceOutcome (F.lowOrder i) (F.base+i) (F.D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (F.fullOrder i)) →
          1-1/(F.lowOrder i:ℝ)≤totalVariation (F.D i).law q) ∧
      (∀ i,∃ q : SourceOutcome (F.lowOrder i) (F.base+i) (F.D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (F.fullOrder i)) ∧
          totalVariation (F.D i).law q=1-1/(F.lowOrder i:ℝ)) := by
  classical
  let F : DyadicLawFamily := Classical.choice dyadic_law_family_exists
  have hn := dyadic_family_numeric_rates F
  have hi (i : ℕ) := dyadic_family_law_identities F i
  have hfullp (i : ℕ) : (0:ℝ)<F.fullOrder i := by
    change (0:ℝ)<((F.lowOrder i*F.seedOrder i:ℕ):ℝ)
    exact_mod_cast Nat.mul_pos (dyadic_family_orders F i).1
      (pow_pos (by decide : 0<2) (F.base+i))
  have hN : Tendsto (fun i => (F.fullOrder i:ℝ)) atTop atTop := by
    have ht := Real.tendsto_exp_atTop.comp hn.1
    simpa only [Function.comp_def,Real.exp_log (hfullp _)] using ht
  have hr : Tendsto (fun i => (F.lowOrder i:ℝ)/(F.seedOrder i:ℝ)) atTop (nhds 1) := by
    simpa only [DyadicLawFamily.lowOrder,DyadicLawFamily.seedOrder,DyadicLawFamily.gapOrder,Nat.cast_pow,Nat.cast_ofNat] using F.ratio
  have hd := sharp_distance_tends_one F.lowOrder F.seedOrder
    (fun i => (dyadic_family_orders F i).1) (fun i => (dyadic_family_orders F i).2.1) hr
  refine ⟨F,?_,hN,?_,?_,?_,?_,?_,?_,hn.2.2.2.2.1,hd,?_,?_⟩
  · intro i
    exact ⟨(hi i).1,(hi i).2.1,(hi i).2.2.1,(hi i).2.2.2.1,(hi i).2.2.2.2.1⟩
  · convert hr using 1
    funext i
    have ht := (F.D i).ratio
    simpa only [CompleteLawData.law,DyadicLawFamily.lowOrder,DyadicLawFamily.seedOrder,DyadicLawFamily.gapOrder,Nat.cast_pow,Nat.cast_ofNat] using ht
  · convert hn.2.1 using 1
    funext i
    rw [(hi i).2.2.2.2.2.1]
  · convert hn.2.2.1 using 1
    funext i
    rw [(hi i).2.2.2.2.2.2.1]
  · convert hn.2.2.2.1 using 1
    funext i
    rw [(hi i).2.2.2.2.2.2.2.1]
  · intro α hα
    convert hn.2.2.2.2.2 using 1
    funext i
    rw [(hi i).2.2.2.2.2.2.2.2.1 α hα]
  · convert hn.2.2.2.2.2 using 1
    funext i
    rw [(hi i).2.2.2.2.2.2.2.2.2]
  · intro i
    exact (F.D i).properties.2.2.2.2.2.2.1
  · intro i
    exact (F.D i).properties.2.2.2.2.2.2.2

end
end EntropyDesigns.ProjectInstability
