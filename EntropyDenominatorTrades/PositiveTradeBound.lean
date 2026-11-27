/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.MomentTrade
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
noncomputable section

theorem reduced_trade_prime_factor_volume_bound {J : Type*} [Fintype J] [DecidableEq J]
    (A B : Matrix J J ℤ) (hA : A.IsHadamard) (c₀ : J) (S : Finset J)
    (ht : IsReducedNormalizedObservationTrade A B c₀ S)
    (hS : S.Nonempty) (hr : S.card<Fintype.card J)
    (m : ℕ) (hm : 1<m) (hodd : Odd m) (hcard : Fintype.card J=4*m) :
    (m.minFac:ℝ)≤(S.card:ℝ)^((S.card:ℝ)/2)/(2:ℝ)^(S.card-1) := by
  classical
  have hn : 0<Fintype.card J := by omega
  have hB := reduced_observation_trade_is_hadamard A B hA hn c₀ S ht
  obtain ⟨ha,hb,hs,hretain,hnew,hfirst,hsecond⟩ := ht
  obtain ⟨i,hi⟩ := hS
  have ho (j : J) (hj : j∉S) : (∑ k,B i k*A j k)=0 := by
    have hne : i≠j := by intro h;subst j;exact hj hi
    simpa only [hretain j hj,hne,ite_false] using integral_hadamard_row_gram B hB i j
  have hspan := retained_orthogonality_forces_deleted_span A hA hn S (B i) ho
  let e : S ↪ J := ⟨Subtype.val,Subtype.val_injective⟩
  have hrS : Fintype.card S<Fintype.card J := by simpa only [Fintype.card_coe] using hr
  have hnot (j : S) : B i≠A (e j) ∧ B i≠fun k => -A (e j) k := by
    refine ⟨hnew i hi (e j) j.property,?_⟩
    intro he
    have hh := congrFun he c₀
    change B i c₀= -A (e j) c₀ at hh
    rw [hb,ha] at hh
    norm_num at hh
  have h := hadamard_new_row_denominator_obstruction A hA e hrS (B i) (hs i)
    hspan hnot m hm hodd hcard
  simpa only [Fintype.card_coe] using h.1

theorem no_reduced_trade_below_determinant_threshold {J : Type*} [Fintype J] [DecidableEq J]
    (A B : Matrix J J ℤ) (hA : A.IsHadamard) (c₀ : J) (S : Finset J)
    (ht : IsReducedNormalizedObservationTrade A B c₀ S)
    (m R : ℕ) (hm : 1<m) (hodd : Odd m) (hcard : Fintype.card J=4*m)
    (hR : R<Fintype.card J) (hdegree : S.card≤R)
    (hbound : ∀ r : ℕ,1≤r → r≤R →
      (r:ℝ)^((r:ℝ)/2)/(2:ℝ)^(r-1)<(m.minFac:ℝ)) : S=∅ := by
  by_contra hne
  have hS := Finset.nonempty_iff_ne_empty.mpr hne
  have hb := reduced_trade_prime_factor_volume_bound A B hA c₀ S ht hS
    (hdegree.trans_lt hR) m hm hodd hcard
  exact (not_lt_of_ge hb) (hbound S.card (Finset.card_pos.mpr hS) hdegree)

end
end EntropyDesigns.DenominatorTrades
