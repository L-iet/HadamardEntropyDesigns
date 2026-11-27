/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.PositiveTradeBound
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
noncomputable section

theorem normalized_determinant_envelope_at_four_mul (m : ℕ) (hm : 0<m) :
    (m:ℝ)≤((4*m:ℕ):ℝ)^(((4*m:ℕ):ℝ)/2)/(2:ℝ)^(4*m-1) := by
  have he : (((4*m:ℕ):ℝ)/2)=((2*m:ℕ):ℝ) := by push_cast;ring
  rw [he,Real.rpow_natCast]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2^(4*m-1))).mpr
  let k : ℕ := 2*m-1
  have htwo : 2*m=k+1 := by dsimp [k];omega
  have hfour : 4*m-1=2*k+1 := by dsimp [k];omega
  have hbase : (4:ℝ)≤((4*m:ℕ):ℝ) := by exact_mod_cast (show 4≤4*m by omega)
  have hb : (2:ℝ)^(2*k)≤((4*m:ℕ):ℝ)^k := by
    calc
      _=(4:ℝ)^k := by rw [pow_mul];norm_num
      _≤_ := pow_le_pow_left₀ (by norm_num) hbase k
  rw [hfour,pow_succ,htwo,pow_succ]
  have hn : ((4*m:ℕ):ℝ)=4*(m:ℝ) := by push_cast;ring
  have hs := mul_le_mul_of_nonneg_right hb (show (0:ℝ)≤((4*m:ℕ):ℝ) by positivity)
  rw [hn] at hs ⊢
  have hp : (0:ℝ)≤2^(2*k) := by positivity
  have hmR : (0:ℝ)≤(m:ℝ) := by positivity
  nlinarith

theorem determinant_threshold_forces_degree_lt_order (m R : ℕ) (hm : 0<m)
    (hbound : ∀ r : ℕ,1≤r → r≤R →
      (r:ℝ)^((r:ℝ)/2)/(2:ℝ)^(r-1)<(m.minFac:ℝ)) : R<4*m := by
  by_contra h
  have hR : 4*m≤R := by omega
  have hb := hbound (4*m) (by omega) hR
  have hp : (m.minFac:ℝ)≤(m:ℝ) := by exact_mod_cast Nat.minFac_le hm
  exact (not_lt_of_ge (hp.trans (normalized_determinant_envelope_at_four_mul m hm))) hb

theorem bounded_degree_observation_trades_are_isolated {J : Type*} [Fintype J] [DecidableEq J]
    (A B : Matrix J J ℤ) (hA : A.IsHadamard) (c₀ : J) (S : Finset J)
    (ht : IsReducedNormalizedObservationTrade A B c₀ S)
    (m R : ℕ) (hm : 1<m) (hodd : Odd m) (hcard : Fintype.card J=4*m)
    (hdegree : S.card≤R)
    (hbound : ∀ r : ℕ,1≤r → r≤R →
      (r:ℝ)^((r:ℝ)/2)/(2:ℝ)^(r-1)<(m.minFac:ℝ)) : S=∅ := by
  have hR : R<Fintype.card J := by
    rw [hcard]
    exact determinant_threshold_forces_degree_lt_order m R (by omega) hbound
  exact no_reduced_trade_below_determinant_threshold A B hA c₀ S ht m R hm hodd hcard hR hdegree hbound

end
end EntropyDesigns.DenominatorTrades
