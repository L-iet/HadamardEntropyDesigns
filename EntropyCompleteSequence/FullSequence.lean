/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCompleteSequence.CompleteLawData
@[expose] public section
namespace EntropyDesigns.RelativeSequence
noncomputable section
open SupportFace ConcentratedFamily
open Filter Set
open scoped Topology

/-- One unconditional family simultaneously has exact moments, uniform
vertex laws, strict local collision maximality, asymptotically optimal
collision and every positive-order entropy, and sharp distance tending
to one from all Hadamard mixtures. Its orders tend to infinity and are
actual Hadamard orders. -/
theorem full_unconditional_sequence :
    ∃ a s : ℕ → ℕ, ∃ D : (i : ℕ) → CompleteLawData (12^(a i)) (s i),
      Tendsto (fun i => 12^(a i)*2^(s i)) atTop atTop ∧
      (∀ i, ∃ H : Matrix (Fin (12^(a i)*2^(s i))) (Fin (12^(a i)*2^(s i))) ℤ,
        Matrix.IsHadamard H) ∧
      (∀ i, sourceFeasible (D i).i0 (D i).law ∧
        (D i).law ∈ Set.extremePoints ℝ
          {q : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ | sourceFeasible (D i).i0 q}) ∧
      Tendsto (fun i => collision (D i).law / collision (D i).optimizer) atTop (nhds 1) ∧
      Tendsto (fun i => ((12^(a i)*2^(s i):ℕ):ℝ) * collision (D i).law) atTop (nhds 1) ∧
      (∀ i, ∀ q : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (12^(a i)*2^(s i))) →
          1-1/((12^(a i):ℕ):ℝ) ≤ totalVariation (D i).law q) ∧
      (∀ i, ∃ q : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (12^(a i)*2^(s i))) ∧
          totalVariation (D i).law q=1-1/((12^(a i):ℕ):ℝ)) ∧
      Tendsto (fun i => 1-1/((12^(a i):ℕ):ℝ)) atTop (nhds 1) ∧
      (∀ α : ℝ, 0<α →
        (∀ i, ∀ w : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ,
          sourceFeasible (D i).i0 w → renyiEntropy (D i).optimizer α ≤ renyiEntropy w α) ∧
        Tendsto (fun i => renyiEntropy (D i).law α-renyiEntropy (D i).optimizer α)
          atTop (nhds 0)) ∧
      (∀ i, ∀ w : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ,
        sourceFeasible (D i).i0 w → minEntropy (D i).optimizer ≤ minEntropy w) ∧
      Tendsto (fun i => minEntropy (D i).law-minEntropy (D i).optimizer) atTop (nhds 0) := by
  classical
  obtain ⟨a,s,ha,hgap,hK,hr,hd,he⟩ := selected_order_limits
  have hdata (i : ℕ) : Nonempty (CompleteLawData (12^(a i)) (s i)) := by
    have hk : 2≤12^(a i) := order_at_least_two (hgap i).1 (hgap i).2.2
    let e : Finset (Fin (s i)) := {⟨0,Nat.pos_of_ne_zero (hgap i).1⟩}
    let i0 : Fin (12^(a i)) := ⟨0,lt_of_lt_of_le (by decide : 0<2) hk⟩
    obtain ⟨K,hKi⟩ := hK i
    exact complete_law_data_exists hk (hgap i).2.1 (hgap i).2.2 e
      (Finset.singleton_nonempty _) i0 K hKi
  let D : (i : ℕ) → CompleteLawData (12^(a i)) (s i) := fun i => Classical.choice (hdata i)
  have hex : Tendsto (fun i => Real.log ((2:ℝ)^(s i)/((12^(a i):ℕ):ℝ))) atTop (nhds 0) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using he
  refine ⟨a,s,D,?_,?_,?_,?_,?_,?_,?_,hd,?_,?_,?_⟩
  · apply tendsto_atTop_mono (fun i => ?_) tendsto_id
    have ha' : a i < 12^(a i) := Nat.lt_pow_self (by decide)
    have hh : 1≤2^(s i) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
    have hm := Nat.mul_le_mul_left (12^(a i)) hh
    simp only [Nat.mul_one] at hm
    exact le_trans (le_trans (ha i) ha'.le) hm
  · intro i
    obtain ⟨K,hKi⟩ := hK i
    exact known_scaled_hadamard_exists (D i).i0 K hKi
  · intro i
    exact ⟨(D i).properties.1,(D i).vertex⟩
  · have heq : (fun i => collision (D i).law / collision (D i).optimizer)=
        (fun i => ((12^(a i):ℕ):ℝ)/((2^(s i):ℕ):ℝ)) := by
      funext i
      simpa only [CompleteLawData.law,Nat.cast_pow,Nat.cast_ofNat] using (D i).ratio
    rw [heq]
    exact hr
  · have hpoint (i : ℕ) : ((12^(a i)*2^(s i):ℕ):ℝ) * collision (D i).law =
        ((12^(a i):ℕ):ℝ)/((2^(s i):ℕ):ℝ) := by
      have hh := (D i).ratio
      change collision (D i).law / collision (D i).optimizer = _ at hh
      rw [(D i).optimizer_collision] at hh
      simpa only [one_div,div_inv_eq_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_comm] using hh
    have heq := funext hpoint
    rw [heq]
    exact hr
  · intro i
    exact (D i).properties.2.2.2.2.2.2.1
  · intro i
    exact (D i).properties.2.2.2.2.2.2.2
  · intro α hα
    refine ⟨?_,?_⟩
    · intro i w hw
      rw [(D i).entropy_optimizer α hα]
      exact (source_all_entropy_lower (D i).i0 w hw).1 α hα
    · have heq : (fun i => renyiEntropy (D i).law α-renyiEntropy (D i).optimizer α)=
          (fun i => Real.log ((2:ℝ)^(s i)/((12^(a i):ℕ):ℝ))) := by
        funext i
        exact (D i).entropy_excess α hα
      rw [heq]
      exact hex
  · intro i w hw
    rw [(D i).minentropy_optimizer]
    exact (source_all_entropy_lower (D i).i0 w hw).2
  · have heq : (fun i => minEntropy (D i).law-minEntropy (D i).optimizer)=
        (fun i => Real.log ((2:ℝ)^(s i)/((12^(a i):ℕ):ℝ))) := by
      funext i
      exact (D i).minentropy_excess
    rw [heq]
    exact hex

end
end EntropyDesigns.RelativeSequence
