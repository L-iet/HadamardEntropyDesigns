/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPrimeExponentRigidity.PrimePowerFamily
public import EntropyPrimeExponentRigidity.EnvelopeEstimates
public import EntropyDenominatorTrades.EnvelopeIsolation
public import Mathlib.Data.Nat.Prime.Infinite
@[expose] public section
namespace EntropyDesigns.PrimeExponentRigidity
noncomputable section

/-- Every normalized sign-coordinate observation fiber at this order is
isolated under reduced degree-two-moment-preserving moves of degree at most R. -/
def IsRigidOrderAtDegree (n R : ℕ) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) ℤ,∀ c₀ : Fin n,∀ S : Finset (Fin n),
    A.IsHadamard → DenominatorTrades.IsReducedNormalizedObservationTrade A B c₀ S →
    S.card≤R → S=∅

theorem exponent_lt_prime_power_order (k : ℕ) : k<primePowerOrder k := by
  induction k with
  | zero => norm_num [primePowerOrder]
  | succ k ih =>
    unfold primePowerOrder at ih ⊢
    rw [pow_succ]
    have hp : 0<3^k := pow_pos (by decide) k
    omega

theorem prime_exponent_rigid_above_bound (k R : ℕ) (hk : k.Prime) (hko : Odd k)
    (hlarge : (R+1)^(R+1)<k) : IsRigidOrderAtDegree (primePowerOrder k) R := by
  obtain ⟨hfour,hmOdd,hm,hres⟩ := prime_power_parameter_properties k hk hko
  have hrough := prime_power_parameter_roughness k hk hko
  have hK : ((((R+1)^(R+1)):ℕ):ℝ)<(k:ℝ) := by exact_mod_cast hlarge
  have hmin : (k:ℝ)≤((primePowerOddParameter k).minFac:ℝ) := by
    exact_mod_cast (show k≤(primePowerOddParameter k).minFac by omega)
  intro A B c₀ S hA ht hdegree
  have hbound (d : ℕ) (hd : 1≤d) (hdR : d≤R) :
      (d:ℝ)^((d:ℝ)/2)/(2:ℝ)^(d-1)<((primePowerOddParameter k).minFac:ℝ) := by
    have hf := determinant_envelope_le_integer_bound R d hd hdR
    exact (hf.trans_lt hK).trans_le hmin
  have hcard : Fintype.card (Fin (primePowerOrder k))=4*primePowerOddParameter k := by
    simpa only [Fintype.card_fin] using hfour.symm
  exact DenominatorTrades.bounded_degree_observation_trades_are_isolated A B hA c₀ S ht
    (primePowerOddParameter k) R hm hmOdd hcard hdegree hbound

theorem unbounded_known_rigid_orders (R N : ℕ) :
    ∃ n : ℕ,N<n ∧ n%8=4 ∧
      (∃ A : Matrix (Fin n) (Fin n) ℤ,A.IsHadamard) ∧ IsRigidOrderAtDegree n R := by
  let bound := max (N+3) ((R+1)^(R+1)+3)
  obtain ⟨k,hbound,hk⟩ := Nat.exists_infinite_primes bound
  have hN : N+3≤k := (Nat.le_max_left _ _).trans hbound
  have hR : (R+1)^(R+1)+3≤k := (Nat.le_max_right _ _).trans hbound
  have hko : Odd k := hk.odd_of_ne_two (by omega)
  obtain ⟨_,_,_,hres⟩ := prime_power_parameter_properties k hk hko
  exact ⟨primePowerOrder k,lt_trans (by omega) (exponent_lt_prime_power_order k),hres,
    paley_prime_exponent_order k hko,prime_exponent_rigid_above_bound k R hk hko (by omega)⟩

theorem infinitely_many_known_rigid_orders (R : ℕ) :
    Set.Infinite {n : ℕ | n%8=4 ∧
      (∃ A : Matrix (Fin n) (Fin n) ℤ,A.IsHadamard) ∧ IsRigidOrderAtDegree n R} := by
  classical
  intro hf
  obtain ⟨N,hN⟩ := hf.bddAbove
  obtain ⟨n,hn,hres,hA,hRigid⟩ := unbounded_known_rigid_orders R N
  exact (not_le_of_gt hn) (hN ⟨hres,hA,hRigid⟩)

end
end EntropyDesigns.PrimeExponentRigidity
