/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPrimeExponentRigidity.QuantitativeFibers
@[expose] public section
namespace EntropyDesigns.PrimeExponentRigidity
noncomputable section
open Filter

def selectedExponent (i : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (i+3))

def selectedOrder (i : ℕ) : ℕ := primePowerOrder (selectedExponent i)

theorem selected_exponent_properties (i : ℕ) :
    i+3≤selectedExponent i ∧ (selectedExponent i).Prime ∧ Odd (selectedExponent i) := by
  have h := Nat.find_spec (Nat.exists_infinite_primes (i+3))
  change i+3≤selectedExponent i ∧ (selectedExponent i).Prime at h
  exact ⟨h.1,h.2,h.2.odd_of_ne_two (by omega)⟩

theorem selected_order_properties (i : ℕ) :
    (selectedOrder i)%8=4 ∧
      ∃ A : Matrix (Fin (selectedOrder i)) (Fin (selectedOrder i)) ℤ,A.IsHadamard := by
  obtain ⟨hlo,hprime,hodd⟩ := selected_exponent_properties i
  exact ⟨(prime_power_parameter_properties _ hprime hodd).2.2.2,
    paley_prime_exponent_order _ hodd⟩

theorem selected_order_tendsto : Tendsto selectedOrder atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop N] with i hi
  obtain ⟨hlo,hprime,hodd⟩ := selected_exponent_properties i
  have hg := exponent_lt_prime_power_order (selectedExponent i)
  change N≤primePowerOrder (selectedExponent i)
  omega

theorem quantitative_infinite_rigidity_subsequence :
    ∃ n : ℕ → ℕ,Tendsto n atTop atTop ∧
      (∀ i,(n i)%8=4 ∧ ∃ A : Matrix (Fin (n i)) (Fin (n i)) ℤ,A.IsHadamard) ∧
      ∀ epsilon : ℝ,0<epsilon → ∀ᶠ i : ℕ in atTop,
      ∀ A B : Matrix (Fin (n i)) (Fin (n i)) ℤ,∀ c₀ : Fin (n i),∀ S : Finset (Fin (n i)),
      A.IsHadamard → DenominatorTrades.IsReducedNormalizedObservationTrade A B c₀ S →
      S.Nonempty →
      (2-epsilon)*Real.log (Real.log (n i:ℝ))/Real.log (Real.log (Real.log (n i:ℝ)))≤(S.card:ℝ) := by
  refine ⟨selectedOrder,selected_order_tendsto,selected_order_properties,?_⟩
  intro epsilon hepsilon
  obtain ⟨K,hK⟩ := prime_exponent_quantitative_trade_bound epsilon hepsilon
  filter_upwards [eventually_ge_atTop K] with i hi
  obtain ⟨hlo,hprime,hodd⟩ := selected_exponent_properties i
  have hk : K≤selectedExponent i := by omega
  intro A B c₀ S hA ht hS
  change (2-epsilon)*orderLogLog (selectedExponent i)/Real.log (orderLogLog (selectedExponent i))≤(S.card:ℝ)
  exact hK (selectedExponent i) hk hprime hodd A B c₀ S hA ht hS

end
end EntropyDesigns.PrimeExponentRigidity
