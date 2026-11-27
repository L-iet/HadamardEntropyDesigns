/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyGapTransfer.IndexedSelection
@[expose] public section
namespace EntropyDesigns.GapTransfer
noncomputable section
open Filter Asymptotics Set RelativeSequence SupportFace
open scoped Topology

/-- The full uniform-gap transfer: actual laws at every sufficiently large
dyadic seed order, actual Hadamard orders, exact support/collisions, ratio
convergence, all three claimed BigTheta rates, and sharp attained distance. -/
theorem uniform_hadamard_gap_transfer (G : ℝ → ℝ)
    (hG : G =o[atTop] (fun x : ℝ => x))
    (hpos : ∀ x : ℝ,0≤x → 0≤G x) (hmono : MonotoneOn G (Ici 0))
    (hgap : uniformGapInput G) :
    ∃ S : ℕ,∃ k : ℕ → ℕ,∃ D : (i : ℕ) → CompleteLawData (k i) (S+i),
      (∀ i : ℕ,knownHadamardOrder (k i) ∧ knownHadamardOrder (k i*2^(S+i)) ∧
        2*dyadicBuffer G (S+i)≤(2:ℝ)^(S+i)-(k i:ℝ) ∧
        (2:ℝ)^(S+i)-(k i:ℝ)≤3*dyadicBuffer G (S+i)) ∧
      (∀ i : ℕ,(Concentration.observedAtoms (D i).law).card=(2^(S+i))^2 ∧
        collision (D i).law=1/((2:ℝ)^(S+i))^2 ∧
        collision (D i).optimizer=1/((k i*2^(S+i):ℕ):ℝ)) ∧
      Tendsto (fun i => (k i:ℝ)/(2:ℝ)^(S+i)) atTop (nhds 1) ∧
      Tendsto (fun i => collision (D i).law/collision (D i).optimizer) atTop (nhds 1) ∧
      ((fun i => 1-collision (D i).law/collision (D i).optimizer)
        =Θ[atTop] (fun i => dyadicBuffer G (S+i)/(2:ℝ)^(S+i))) ∧
      ((fun i => collision (D i).optimizer-collision (D i).law)
        =Θ[atTop] (fun i => dyadicBuffer G (S+i)/((2:ℝ)^(S+i))^3)) ∧
      ((fun i => ((Concentration.observedAtoms (D i).law).card:ℝ)-((k i*2^(S+i):ℕ):ℝ))
        =Θ[atTop] (fun i => (2:ℝ)^(S+i)*dyadicBuffer G (S+i))) ∧
      (∀ i,∀ q : SourceOutcome (k i) (S+i) (D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k i*2^(S+i))) →
          1-1/(k i:ℝ)≤totalVariation (D i).law q) ∧
      (∀ i,∃ q : SourceOutcome (k i) (S+i) (D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k i*2^(S+i))) ∧
          totalVariation (D i).law q=1-1/(k i:ℝ)) ∧
      Tendsto (fun i => 1-1/(k i:ℝ)) atTop (nhds 1) := by
  classical
  obtain ⟨S,k,D,hselect⟩ := indexed_buffered_laws G hG hpos hmono hgap
  have ha (i : ℕ) : 0<dyadicBuffer G (S+i) := dyadic_buffer_positive G hpos _
  have hh (i : ℕ) : (0:ℝ)<(2:ℝ)^(S+i) := pow_pos (by norm_num) _
  have hkl (i : ℕ) : (k i:ℝ)<(2:ℝ)^(S+i) := by
    have hlow := (hselect i).2.1
    linarith [ha i]
  have hhalf (i : ℕ) : (2:ℝ)^(S+i)/2<(k i:ℝ) := by
    have hup := (hselect i).2.2.1
    have hsmall := (hselect i).2.2.2
    linarith
  have hr (i : ℕ) := complete_law_rate_bounds (D i) (dyadicBuffer G (S+i)) (ha i).le
    (hhalf i) (hkl i) (hselect i).2.1 (hselect i).2.2.1
  have hthetaR : (fun i => 1-collision (D i).law/collision (D i).optimizer)
      =Θ[atTop] (fun i => dyadicBuffer G (S+i)/(2:ℝ)^(S+i)) := by
    apply isTheta_of_nonnegative_bounds _ _ 2 3 (by norm_num)
    · intro i;exact div_nonneg (ha i).le (hh i).le
    · intro i;simpa only [mul_div_assoc] using (hr i).1.1
    · intro i;simpa only [mul_div_assoc] using (hr i).1.2
  have hthetaA : (fun i => collision (D i).optimizer-collision (D i).law)
      =Θ[atTop] (fun i => dyadicBuffer G (S+i)/((2:ℝ)^(S+i))^3) := by
    apply isTheta_of_nonnegative_bounds _ _ 2 6 (by norm_num)
    · intro i;exact div_nonneg (ha i).le (pow_nonneg (hh i).le _)
    · intro i;simpa only [mul_div_assoc] using (hr i).2.1.1
    · intro i;simpa only [mul_div_assoc] using (hr i).2.1.2
  have hthetaS : (fun i => ((Concentration.observedAtoms (D i).law).card:ℝ)-((k i*2^(S+i):ℕ):ℝ))
      =Θ[atTop] (fun i => (2:ℝ)^(S+i)*dyadicBuffer G (S+i)) := by
    apply isTheta_of_nonnegative_bounds _ _ 2 3 (by norm_num)
    · intro i;exact mul_nonneg (hh i).le (ha i).le
    · intro i;simpa only [mul_assoc] using (hr i).2.2.1
    · intro i;simpa only [mul_assoc] using (hr i).2.2.2
  have hindex : Tendsto (fun i : ℕ => S+i) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_add_left i S) tendsto_id
  have hscale : Tendsto (fun i => dyadicBuffer G (S+i)/(2:ℝ)^(S+i)) atTop (nhds 0) := by
    simpa only [Function.comp_def] using (dyadic_buffer_ratio_zero G hG).comp hindex
  have hthree : Tendsto (fun i => 3*(dyadicBuffer G (S+i)/(2:ℝ)^(S+i))) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hscale
  have hfzero : Tendsto (fun i => 1-collision (D i).law/collision (D i).optimizer)
      atTop (nhds 0) := by
    apply squeeze_zero _ _ hthree
    · intro i
      exact (div_nonneg (mul_nonneg (by norm_num) (ha i).le) (hh i).le).trans (hr i).1.1
    · intro i
      simpa only [mul_div_assoc] using (hr i).1.2
  have hc : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hratio := hc.sub hfzero
  change Tendsto (fun i => 1-(1-collision (D i).law/collision (D i).optimizer)) atTop (nhds (1-0)) at hratio
  have hcancel : (fun i => 1-(1-collision (D i).law/collision (D i).optimizer))=
      (fun i => collision (D i).law/collision (D i).optimizer) := by funext i;ring
  rw [hcancel] at hratio
  simp only [sub_zero] at hratio
  have hratEq : (fun i => collision (D i).law/collision (D i).optimizer)=
      (fun i => (k i:ℝ)/(2:ℝ)^(S+i)) := by
    funext i
    simpa only [CompleteLawData.law] using (D i).ratio
  have hkRatio := hratio
  rw [hratEq] at hkRatio
  have hkPos (i : ℕ) : 0<k i := Nat.zero_lt_of_lt (D i).i0.isLt
  have hkLt (i : ℕ) : k i<2^(S+i) := by exact_mod_cast hkl i
  have hkRatioNat : Tendsto (fun i => (k i:ℝ)/((2^(S+i):ℕ):ℝ)) atTop (nhds 1) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hkRatio
  have hd := sharp_distance_tends_one k (fun i => 2^(S+i)) hkPos hkLt hkRatioNat
  refine ⟨S,k,D,?_,?_,hkRatio,hratio,hthetaR,hthetaA,hthetaS,?_,?_,hd⟩
  · intro i
    obtain ⟨K,hK⟩ := (hselect i).1
    exact ⟨⟨K,hK⟩,known_scaled_hadamard_exists (D i).i0 K hK,(hselect i).2.1,(hselect i).2.2.1⟩
  · intro i
    refine ⟨complete_law_support_card (D i),?_,(D i).optimizer_collision⟩
    simpa only [CompleteLawData.law] using (D i).properties.2.2.2.1
  · intro i
    exact (D i).properties.2.2.2.2.2.2.1
  · intro i
    exact (D i).properties.2.2.2.2.2.2.2

end
end EntropyDesigns.GapTransfer
