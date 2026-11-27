/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPrimeTransfer.PolynomialLawRates
@[expose] public section
namespace EntropyDesigns.PrimeTransfer
noncomputable section
open Filter Asymptotics Set RelativeSequence SupportFace GapTransfer
open scoped Topology

/-- Full ordinary-prime-gap stability transfer, conditional only on the
stated ordinary prime interval hypothesis. No analytic input is assumed
under another name and no numerical threshold is claimed. -/
theorem ordinary_prime_gap_transfer (θ : ℝ) (hθ0 : 0<θ) (hθ1 : θ<1)
    (hprime : ∀ᶠ y : ℝ in atTop, ∃ p : ℕ,
      p.Prime ∧ y-y^θ≤(p:ℝ) ∧ (p:ℝ)≤y) :
    ∃ S : ℕ,∃ k : ℕ → ℕ,∃ D : (i : ℕ) → CompleteLawData (k i) (S+i),
      (∀ i : ℕ,knownHadamardOrder (k i) ∧ knownHadamardOrder (k i*2^(S+i)) ∧
        2*dyadicBuffer (scaledPowerGap θ) (S+i)≤(2:ℝ)^(S+i)-(k i:ℝ) ∧
        (2:ℝ)^(S+i)-(k i:ℝ)≤3*dyadicBuffer (scaledPowerGap θ) (S+i)) ∧
      (∀ i : ℕ,(Concentration.observedAtoms (D i).law).card=(2^(S+i))^2 ∧
        collision (D i).law=1/((2:ℝ)^(S+i))^2 ∧
        collision (D i).optimizer=1/((k i*2^(S+i):ℕ):ℝ)) ∧
      Tendsto (fun i => (k i:ℝ)/(2:ℝ)^(S+i)) atTop (nhds 1) ∧
      Tendsto (fun i => collision (D i).law/collision (D i).optimizer) atTop (nhds 1) ∧
      ((fun i => 1-collision (D i).law/collision (D i).optimizer)
        =Θ[atTop] (fun i => ((k i*2^(S+i):ℕ):ℝ)^((θ-1)/2))) ∧
      ((fun i => collision (D i).optimizer-collision (D i).law)
        =Θ[atTop] (fun i => ((k i*2^(S+i):ℕ):ℝ)^((θ-3)/2))) ∧
      ((fun i => ((Concentration.observedAtoms (D i).law).card:ℝ)-((k i*2^(S+i):ℕ):ℝ))
        =Θ[atTop] (fun i => (2:ℝ)^(S+i)*dyadicBuffer (scaledPowerGap θ) (S+i))) ∧
      (∀ i,∀ q : SourceOutcome (k i) (S+i) (D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k i*2^(S+i))) →
          1-1/(k i:ℝ)≤totalVariation (D i).law q) ∧
      (∀ i,∃ q : SourceOutcome (k i) (S+i) (D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k i*2^(S+i))) ∧
          totalVariation (D i).law q=1-1/(k i:ℝ)) ∧
      ((fun i => 1/(k i:ℝ)) =Θ[atTop] (fun i => ((k i*2^(S+i):ℕ):ℝ)^(-(1:ℝ)/2))) ∧
      Tendsto (fun i => 1-1/(k i:ℝ)) atTop (nhds 1) := by
  have hp := scaled_power_nonnegative_monotone θ hθ0
  have hgap : uniformGapInput (scaledPowerGap θ) :=
    power_prime_gap_known_orders θ hθ0 hθ1 hprime
  obtain ⟨S,k,D,hknown,hexact,hkr,hcr,hrel,habs,hsupp,hlower,hatt,hd⟩ :=
    uniform_hadamard_gap_transfer (scaledPowerGap θ) (scaled_power_sublinear θ hθ1)
      hp.1 hp.2 hgap
  have hkp (i : ℕ) : 0<k i := Nat.zero_lt_of_lt (D i).i0.isLt
  have rates := polynomial_full_order_rates θ hθ0 S k hkp hkr _ _ hrel habs
  refine ⟨S,k,D,hknown,hexact,hkr,hcr,?_,?_,hsupp,hlower,hatt,?_,hd⟩
  · simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using rates.1
  · simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using rates.2.1
  · simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using rates.2.2

end
end EntropyDesigns.PrimeTransfer
