/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.RetainedSpan
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
noncomputable section

/-- A reduced observation trade written in normalized sign coordinates.
The final two fields preserve precisely the moments of degrees one and two. -/
def IsReducedNormalizedObservationTrade {J : Type*} [Fintype J]
    (A B : Matrix J J ℤ) (c₀ : J) (S : Finset J) : Prop :=
  (∀ r,A r c₀=1) ∧ (∀ r,B r c₀=1) ∧
  (∀ r c,B r c=1 ∨ B r c= -1) ∧
  (∀ r,r∉S → B r=A r) ∧
  (∀ r,r∈S → ∀ t,t∈S → B r≠A t) ∧
  (∀ c,c≠c₀ → (∑ r,B r c)=(∑ r,A r c)) ∧
  (∀ c d,c≠c₀ → d≠c₀ → (∑ r,B r c*B r d)=(∑ r,A r c*A r d))

theorem normalized_moments_preserve_column_gram {J : Type*} [Fintype J]
    [DecidableEq J] (A B : Matrix J J ℤ) (c₀ : J)
    (hA : ∀ r,A r c₀=1) (hB : ∀ r,B r c₀=1)
    (hfirst : ∀ c,c≠c₀ → (∑ r,B r c)=(∑ r,A r c))
    (hsecond : ∀ c d,c≠c₀ → d≠c₀ → (∑ r,B r c*B r d)=(∑ r,A r c*A r d)) :
    B.transpose*B=A.transpose*A := by
  ext c d
  change (∑ r,B r c*B r d)=(∑ r,A r c*A r d)
  by_cases hc : c=c₀
  · subst c
    simp only [hA,hB,one_mul]
    by_cases hd : d=c₀
    · subst d; simp only [hA,hB]
    · exact hfirst d hd
  · by_cases hd : d=c₀
    · subst d
      simp only [hA,hB,mul_one]
      exact hfirst c hc
    · exact hsecond c d hc hd

theorem reduced_observation_trade_is_hadamard {J : Type*} [Fintype J] [DecidableEq J]
    (A B : Matrix J J ℤ) (hA : A.IsHadamard) (hn : 0<Fintype.card J)
    (c₀ : J) (S : Finset J) (ht : IsReducedNormalizedObservationTrade A B c₀ S) :
    B.IsHadamard := by
  obtain ⟨ha,hb,hs,hretain,hnew,hfirst,hsecond⟩ := ht
  have hg := normalized_moments_preserve_column_gram A B c₀ ha hb hfirst hsecond
  have hcol : B.transpose*B=(Fintype.card J:ℤ) • 1 := by
    rw [hg]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.conjTranspose_mul
  have hBt : B.transpose.IsHadamard := by
    apply Matrix.IsHadamard.of_mul_conjTranspose
    · intro i j
      exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hs j i)
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using hcol
    · apply isRegular_iff_ne_zero.mpr
      exact_mod_cast hn.ne'
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using hBt.conjTranspose

end
end EntropyDesigns.DenominatorTrades
