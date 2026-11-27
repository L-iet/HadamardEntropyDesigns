/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCompleteSequence.CompleteWitness
public import EntropyCompleteSequence.UnconditionalLaws
@[expose] public section
namespace EntropyDesigns.RelativeSequence
noncomputable section
open SupportFace ConcentratedFamily SpanningSlopes

structure CompleteLawData (k s : ℕ) where
  e : Finset (Fin s)
  he : e.Nonempty
  i0 : Fin k
  hs : s≠0
  t : Fin k → GaloisField 2 s
  ht : Function.Injective t
  properties :
    let p := uniformFiniteLaw (planeSupport hs e i0 t);
          sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
            (planeSupport hs e i0 t).card=(2^s)^2 ∧ collision p=1/((2:ℝ)^s)^2 ∧
            (0<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) ∧
              ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → q≠p →
                ‖q-p‖<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) → collision q<collision p) ∧
            (∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
              (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) ∧
              collision p/collision q=(k:ℝ)/(2:ℝ)^s) ∧
            (∀ q : SourceOutcome k s i0 → ℝ,
              q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
                1-1/(k:ℝ)≤totalVariation p q) ∧
            (∃ q : SourceOutcome k s i0 → ℝ,
              q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
                totalVariation p q=1-1/(k:ℝ))

  vertex : uniformFiniteLaw (planeSupport hs e i0 t) ∈
    Set.extremePoints ℝ {q : SourceOutcome k s i0 → ℝ | sourceFeasible i0 q}
  optimizer : SourceOutcome k s i0 → ℝ
  optimizer_feasible : sourceFeasible i0 optimizer
  optimizer_collision : collision optimizer=1/((k*2^s:ℕ):ℝ)
  optimizer_global : ∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision optimizer
  ratio : collision (uniformFiniteLaw (planeSupport hs e i0 t))/collision optimizer=(k:ℝ)/(2:ℝ)^s
  entropy_optimizer : ∀ α : ℝ,0<α → renyiEntropy optimizer α=Real.log ((k*2^s:ℕ):ℝ)
  minentropy_optimizer : minEntropy optimizer=Real.log ((k*2^s:ℕ):ℝ)
  entropy_excess : ∀ α : ℝ,0<α →
    renyiEntropy (uniformFiniteLaw (planeSupport hs e i0 t)) α-renyiEntropy optimizer α=
      Real.log ((2:ℝ)^s/(k:ℝ))
  minentropy_excess : minEntropy (uniformFiniteLaw (planeSupport hs e i0 t))-minEntropy optimizer=
    Real.log ((2:ℝ)^s/(k:ℝ))

def CompleteLawData.law {k s : ℕ} (D : CompleteLawData k s) : SourceOutcome k s D.i0 → ℝ :=
  uniformFiniteLaw (planeSupport D.hs D.e D.i0 D.t)

theorem complete_law_data_exists {k s : ℕ} (hk : 2≤k)
    (hsu : s≤2^s-k) (hsmall : 2^s-k<2^s/2)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    Nonempty (CompleteLawData k s) := by
  obtain ⟨hs,R,t,ht,hzero,hRcard,hRzero,hRspan,hRcomp,hfull,hvertex,hEnt⟩ :=
    complete_spanning_witness_exists hk hsu hsmall e he i0 K hK
  obtain ⟨q,hq,hCq,hglobal,hratio⟩ := hfull.2.2.2.2.2.1
  have hn : (0:ℝ)<((k*2^s:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.zero_lt_of_lt i0.isLt) (pow_pos (by decide) s)
  have hu := source_uniform_of_collision i0 q hq hCq
  have hqa (α : ℝ) (hα : 0<α) : renyiEntropy q α=Real.log ((k*2^s:ℕ):ℝ) :=
    renyi_all_uniform q _ α hn hα hq.2.1 hu
  have hqm : minEntropy q=Real.log ((k*2^s:ℕ):ℝ) := minEntropy_uniform q _ hn hq.2.1 hu
  have hp := plane_all_entropy hk hs e he i0 t ht
  have hex : Real.log (((2^s)^2:ℕ):ℝ)-Real.log ((k*2^s:ℕ):ℝ)=Real.log ((2:ℝ)^s/(k:ℝ)) := by
    simp only [Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat]
    exact logarithm_entropy_excess (k:ℝ) ((2:ℝ)^s)
      (by exact_mod_cast lt_of_lt_of_le (by decide : 0<2) hk) (by positivity)
  refine ⟨{ e := e
            he := he
            i0 := i0
            hs := hs
            t := t
            ht := ht
            properties := hfull
            vertex := hvertex
            optimizer := q
            optimizer_feasible := hq
            optimizer_collision := hCq
            optimizer_global := hglobal
            ratio := hratio
            entropy_optimizer := hqa
            minentropy_optimizer := hqm
            entropy_excess := ?_
            minentropy_excess := ?_ }⟩
  · intro α hα
    rw [hp.1 α hα,hqa α hα]
    exact hex
  · rw [hp.2,hqm]
    exact hex

theorem known_scaled_hadamard_exists {k s : ℕ} (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    ∃ H : Matrix (Fin (k*2^s)) (Fin (k*2^s)) ℤ,Matrix.IsHadamard H := by
  classical
  let ρ : (Fin k × (Fin s → Bool)) ≃ Fin (k*2^s) :=
    Fintype.equivOfCardEq (by simp)
  let c : BlockSeeds k s := fun _ _ => false
  exact ⟨Matrix.reindex ρ ρ (offsetHadamard ∅ i0 c K),
    (offsetHadamard_isHadamard ∅ i0 c K hK).reindex ρ ρ⟩

end
end EntropyDesigns.RelativeSequence
