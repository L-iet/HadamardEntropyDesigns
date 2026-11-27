/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyRelativeSequence.OrderSequence
public import EntropySpanningSlopes.SpanningExistence
@[expose] public section
namespace EntropyDesigns.RelativeSequence
noncomputable section
open SupportFace ConcentratedFamily
open Filter
open scoped Topology

def FullSpanningWitness (k s : ℕ) (e : Finset (Fin s)) (i0 : Fin k) : Prop :=
  ∃ hs : s≠0,∃ R : Finset (GaloisField 2 s),∃ t : Fin k → GaloisField 2 s,
      Function.Injective t ∧ t i0=0 ∧ R.card=2^s-k ∧ 0∉R ∧
      Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤ ∧
      (∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a) ∧
      let p := uniformFiniteLaw (planeSupport hs e i0 t)
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

theorem relative_spanning_laws (k s : ℕ → ℕ)
    (hk : ∀ i, 2 ≤ k i) (hsu : ∀ i, s i ≤ 2^(s i)-k i)
    (hsmall : ∀ i, 2^(s i)-k i < 2^(s i)/2)
    (hK : ∀ i, ∃ K : Matrix (Fin (k i)) (Fin (k i)) ℤ, Matrix.IsHadamard K)
    (hratio : Tendsto (fun i => (k i:ℝ)/((2^(s i):ℕ):ℝ)) atTop (nhds 1)) :
    (∀ i, ∃ e : Finset (Fin (s i)), ∃ i0 : Fin (k i),
      e.Nonempty ∧ FullSpanningWitness (k i) (s i) e i0) ∧
    Tendsto (fun i => 1-1/(k i:ℝ)) atTop (nhds 1) ∧
    (∀ i, 1/((k i*2^(s i):ℕ):ℝ)-1/(((2^(s i))^2:ℕ):ℝ)=
      ((2^(s i)-k i:ℕ):ℝ)/((k i*(2^(s i))^2:ℕ):ℝ)) := by
  classical
  have hkh (i : ℕ) : k i < 2^(s i) := by
    have hs : s i ≠ 0 := by
      intro hzero
      have hh := hsmall i
      rw [hzero] at hh
      norm_num at hh
    have hbudget := hsu i
    omega
  refine ⟨?_, sharp_distance_tends_one k (fun i => 2^(s i))
    (fun i => lt_of_lt_of_le (by decide : 0<2) (hk i)) hkh hratio, ?_⟩
  · intro i
    have hs : s i ≠ 0 := by
      intro hzero
      have hh := hsmall i
      rw [hzero] at hh
      norm_num at hh
    let e : Finset (Fin (s i)) := {⟨0, Nat.pos_of_ne_zero hs⟩}
    let i0 : Fin (k i) := ⟨0, lt_of_lt_of_le (by decide : 0<2) (hk i)⟩
    have he : e.Nonempty := Finset.singleton_nonempty _
    obtain ⟨K,hKi⟩ := hK i
    exact ⟨e,i0,he,SpanningSlopes.spanning_witness_exists (hk i) (hsu i) (hsmall i) e he i0 K hKi⟩
  · intro i
    exact collision_deficit_identity (lt_of_lt_of_le (by decide : 0<2) (hk i))
      (pow_pos (by decide : 0<(2:ℕ)) _) (hkh i).le

end
end EntropyDesigns.RelativeSequence
