/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPlotkinSupport.GlobalBound
public import Mathlib.Tactic.FieldSimp
@[expose] public section
namespace EntropyDesigns.PlotkinSupport
noncomputable section
open SupportFace
open scoped BigOperators

theorem source_plotkin_distance_bound {k s : ℕ} (hk : k≤2^s)
    (e : Finset (Fin s)) (i0 : Fin k) (p : SourceOutcome k s i0 → ℝ)
    (hp : ∑ x,p x=1) (hsupport : sourceSupported e i0 p)
    (q : SourceOutcome k s i0 → ℝ)
    (hq : q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s))) :
    1-((2^s/(2^s-k+1):ℕ):ℝ)/(k:ℝ)≤totalVariation p q := by
  classical
  have hkpos : 0<k := by have hi := i0.isLt;omega
  have hn : 0<k*2^s := Nat.mul_pos hkpos (pow_pos (by decide) _)
  have hs : ∀ x,x∉observedSupport e i0 → p x=0 := by
    intro y hy
    apply hsupport y
    intro ⟨x,hx⟩
    exact hy (Finset.mem_image.mpr ⟨x,Finset.mem_univ x,hx⟩)
  have hw := SupportWitness.support_witness_all_mixtures observedOrthogonal
    (observedSupport e i0) hn p hp hs q hq
  have hcap : (SupportWitness.orthogonalityNumber observedOrthogonal (observedSupport e i0):ℝ)≤
      ((2^s*(2^s/(2^s-k+1)):ℕ):ℝ) := by
    exact_mod_cast observed_orthogonality_plotkin_bound hk e i0
  have hd := div_le_div_of_nonneg_right hcap (Nat.cast_nonneg (k*2^s))
  have hkreal : (k:ℝ)≠0 := by exact_mod_cast ne_of_gt hkpos
  have hfrac : (((2^s*(2^s/(2^s-k+1)):ℕ):ℝ))/((k*2^s:ℕ):ℝ)=
      ((2^s/(2^s-k+1):ℕ):ℝ)/(k:ℝ) := by
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  rw [hfrac] at hd
  linarith

end
end EntropyDesigns.PlotkinSupport
