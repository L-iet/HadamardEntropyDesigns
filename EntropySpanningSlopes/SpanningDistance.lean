/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySpanningSlopes.CliqueGeometry
public import EntropySpanningSlopes.HadamardNormalization
public import EntropyConcentratedFamily.PartialMixture
@[expose] public section
namespace EntropyDesigns.SpanningSlopes
noncomputable section
open SupportFace ConcentratedFamily
open scoped BigOperators

theorem spanning_plane_all_mixtures_distance_lower {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) (hzero : t i0=0)
    (R : Finset (GaloisField 2 s))
    (hspan : Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤)
    (hcomp : ∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a)
    (hsmall : R.card<2^s/2) (p q : SourceOutcome k s i0 → ℝ)
    (hp : ∑ x,p x=1) (hsupport : ∀ y,y∉planeSupport hs e i0 t → p y=0)
    (hq : q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s))) :
    1-1/(k:ℝ)≤totalVariation p q := by
  classical
  have hkpos : 0<k := by omega
  have hh : 0<2^s := pow_pos (by decide) s
  have h := SupportWitness.support_witness_all_mixtures observedOrthogonal
    (planeSupport hs e i0 t) (Nat.mul_pos hkpos hh) p hp hsupport q hq
  rw [spanning_plane_orthogonality_number hk hs e he i0 t ht hzero R hspan hcomp hsmall] at h
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hkpos.ne'
  have hh0 : (2:ℝ)^s≠0 := pow_ne_zero s (by norm_num)
  have hratio : ((2^s:ℕ):ℝ)/((k*2^s:ℕ):ℝ)=1/(k:ℝ) := by
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  rw [hratio] at h
  exact h

theorem spanning_plane_sharp_distance_of_hadamard {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (hs2 : 2≤s) (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) (hzero : t i0=0)
    (R : Finset (GaloisField 2 s))
    (hspan : Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤)
    (hcomp : ∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a)
    (hsmall : R.card<2^s/2) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    (∀ q : SourceOutcome k s i0 → ℝ,
      q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
        1-1/(k:ℝ)≤totalVariation (uniformFiniteLaw (planeSupport hs e i0 t)) q) ∧
      (∃ q : SourceOutcome k s i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
          totalVariation (uniformFiniteLaw (planeSupport hs e i0 t)) q=1-1/(k:ℝ)) := by
  classical
  let NK := normalizeSignMatrix K i0
  have hNK : Matrix.IsHadamard NK := normalizeSignMatrix_isHadamard K hK i0
  have hfirst : ∀ j,NK i0 j=1 := normalizeSignMatrix_row K hK i0
  have hcol : ∀ a,NK a i0=1 := normalizeSignMatrix_column K hK i0
  have hp := plane_uniform_feasible hk hs e he i0 t ht
  let F := fieldOffsetImage hs i0 t
  have hF : F.Nonempty := by
    apply Finset.card_pos.mp
    dsimp only [F]
    rw [fieldOffsetImage_card hk hs i0 t ht]
    positivity
  constructor
  · intro q hq
    apply spanning_plane_all_mixtures_distance_lower hk hs e he i0 t ht hzero R hspan hcomp hsmall _ q hp.2.1 _ hq
    intro y hy
    simp [uniformFiniteLaw,hy]
  · refine ⟨partialMixture e i0 NK F,partialMixture_mem hs2 e i0 NK hNK hcol F hF,?_⟩
    have h := partialMixture_exact_distance hs2 e i0 NK hNK hfirst hcol F hF
    simpa only [F,planeSupport_offset_partition] using h

end
end EntropyDesigns.SpanningSlopes
