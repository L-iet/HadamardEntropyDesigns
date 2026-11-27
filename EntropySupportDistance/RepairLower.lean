/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SelectedRepair
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

theorem observedOrthogonal_self_false {k s : ℕ} (i0 : Fin k) (x : SourceOutcome k s i0) :
    ¬observedOrthogonal x x := by
  classical
  intro h
  have hs (c : SourceCoordinate k s i0) : bitSign (x c)*bitSign (x c)=1 := by
    cases x c <;> rfl
  unfold observedOrthogonal at h
  simp only [hs,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  have hc : (0:ℤ)≤Fintype.card (SourceCoordinate k s i0) := by positivity
  omega

theorem source_all_repairs_lower {k s b : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (hsize : 2*(k-1)<2^s)
    (x y : Fin b → Fin (k*2^s) → SourceOutcome k s i0)
    (hx : ∀ j i,x j i∈observedSupport e i0)
    (horth : ∀ j i l,i≠l → observedOrthogonal (y j i) (y j l)) :
    ((b*(k*2^s):ℕ):ℝ)*(1-1/(k:ℝ))≤
      ∑ j : Fin b,((Finset.univ.filter (fun i => x j i≠y j i)).card:ℝ) := by
  classical
  have hk : 0<k := Nat.zero_lt_of_lt i0.isLt
  have hn : 0<k*2^s := Nat.mul_pos hk (pow_pos (by decide) s)
  have hy (j : Fin b) : Function.Injective (y j) := by
    intro i l heq
    by_contra hne
    have hh := horth j i l hne
    rw [heq] at hh
    exact observedOrthogonal_self_false i0 (y j l) hh
  have h := SupportWitness.replacement_fraction_bound observedOrthogonal
    (observedSupport e i0) hn x y hx hy horth
  rw [observed_orthogonality_number e i0 hsize] at h
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have hh0 : (2:ℝ)^s≠0 := pow_ne_zero s (by norm_num)
  have hratio : ((2^s:ℕ):ℝ)/((k*2^s:ℕ):ℝ)=1/(k:ℝ) := by
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  rw [hratio] at h
  exact h

end
end EntropyDesigns.SupportFace
