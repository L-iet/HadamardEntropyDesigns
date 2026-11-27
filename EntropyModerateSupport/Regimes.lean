/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyModerateSupport.RegimeWitness
public import EntropyModerateSupport.ModerateScales
@[expose] public section
namespace EntropyDesigns.ModerateSupport
noncomputable section

theorem linear_regime_exists (r : ℕ) (hr : 1≤r)
    (e : Finset (Fin (r+1))) (he : e.Nonempty) (i0 : Fin (2^r)) :
    regimeWitness (2^r) (r+1) e i0 ∧
      (2^(r+1) : ℕ)=2*2^r ∧
      (2^(r+1) : ℕ)^2=2*(2^r*2^(r+1)) := by
  have hk := (ConcentratedFamily.canonical_family_parameters hr).1
  have hh : (2^(r+1) : ℕ)=2*2^r := by rw [Nat.pow_succ,Nat.mul_comm]
  have hsize : 2*(2^r-1)<2^(r+1) := by rw [hh];omega
  refine ⟨regime_witness_exists hk r rfl hsize e he i0,hh,?_⟩
  rw [hh]
  ring

theorem cubic_regime_exists (r : ℕ) (hr : 1≤r)
    (e : Finset (Fin (2*r))) (he : e.Nonempty) (i0 : Fin (2^r)) :
    regimeWitness (2^r) (2*r) e i0 ∧
      (2^(2*r) : ℕ)=(2^r)^2 ∧
      (2^r*2^(2*r) : ℕ)=(2^r)^3 := by
  have hc := ConcentratedFamily.canonical_family_parameters hr
  refine ⟨regime_witness_exists hc.1 r rfl hc.2.1 e he i0,hc.2.2,?_⟩
  rw [hc.2.2]
  ring

end
end EntropyDesigns.ModerateSupport
