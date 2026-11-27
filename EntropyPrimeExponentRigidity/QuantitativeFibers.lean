/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPrimeExponentRigidity.FamilyLogScale
@[expose] public section
namespace EntropyDesigns.PrimeExponentRigidity
noncomputable section

theorem prime_exponent_quantitative_trade_bound (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ K : ℕ,∀ k : ℕ,K≤k → k.Prime → Odd k →
      ∀ A B : Matrix (Fin (primePowerOrder k)) (Fin (primePowerOrder k)) ℤ,
      ∀ c₀ : Fin (primePowerOrder k),∀ S : Finset (Fin (primePowerOrder k)),
      A.IsHadamard → DenominatorTrades.IsReducedNormalizedObservationTrade A B c₀ S →
      S.Nonempty → (2-epsilon)*orderLogLog k/Real.log (orderLogLog k)≤(S.card:ℝ) := by
  obtain ⟨K,hK⟩ := eventual_log_threshold_inputs epsilon hepsilon
  refine ⟨K,?_⟩
  intro k hk hprime hodd A B c₀ S hA ht hS
  obtain ⟨hs,hlogs,hlower⟩ := hK k hk hprime hodd
  obtain ⟨hfour,hmOdd,hm,hres⟩ := prime_power_parameter_properties k hprime hodd
  have hrough := prime_power_parameter_roughness k hprime hodd
  have hp : (0:ℝ)<((primePowerOddParameter k).minFac:ℝ) := by
    exact_mod_cast (show 0<(primePowerOddParameter k).minFac by omega)
  by_contra hnot
  have hsmall : (S.card:ℝ)<(2-epsilon)*orderLogLog k/Real.log (orderLogLog k) := lt_of_not_ge hnot
  have hbound (d : ℕ) (hd : 1≤d) (hdR : d≤S.card) :
      (d:ℝ)^((d:ℝ)/2)/(2:ℝ)^(d-1)<((primePowerOddParameter k).minFac:ℝ) := by
    have hdegree : (d:ℝ)≤(2-epsilon)*orderLogLog k/Real.log (orderLogLog k) :=
      (show (d:ℝ)≤(S.card:ℝ) by exact_mod_cast hdR).trans hsmall.le
    exact determinant_envelope_below_log_threshold _ _ epsilon hp hs hepsilon hlogs hlower d hd hdegree
  have hcard : Fintype.card (Fin (primePowerOrder k))=4*primePowerOddParameter k := by
    simpa only [Fintype.card_fin] using hfour.symm
  have hEmpty := DenominatorTrades.bounded_degree_observation_trades_are_isolated A B hA c₀ S ht
    (primePowerOddParameter k) S.card hm hmOdd hcard le_rfl hbound
  exact hS.ne_empty hEmpty

end
end EntropyDesigns.PrimeExponentRigidity
