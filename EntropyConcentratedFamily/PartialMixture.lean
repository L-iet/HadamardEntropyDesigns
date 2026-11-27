/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SelectedEndpoint
public import EntropySupportDistance.FiniteMixtures
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.ConcentratedFamily
noncomputable section
open SupportFace
open scoped BigOperators

def partialMixture {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (F : Finset (OffsetParameters k s i0)) :
    SourceOutcome k s i0 → ℝ :=
  finiteAverage (fun c : F => uniformFiniteLaw (completedBlock e i0 K c.val))

theorem partialMixture_mem {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) (hcol : ∀ t,K t i0=1)
    (F : Finset (OffsetParameters k s i0)) (hF : F.Nonempty) :
    partialMixture e i0 K F∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) := by
  classical
  obtain ⟨c0,hc0⟩ := hF
  letI : Nonempty F := ⟨⟨c0,hc0⟩⟩
  exact finiteAverage_mem_convexHull _ _ (fun c => completedBlockLaw_mem hs e i0 K hK hcol c.val)

theorem partialMixture_probability {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) (hcol : ∀ t,K t i0=1)
    (F : Finset (OffsetParameters k s i0)) (hF : F.Nonempty) :
    (∀ y,0≤partialMixture e i0 K F y) ∧ ∑ y,partialMixture e i0 K F y=1 := by
  classical
  obtain ⟨c0,hc0⟩ := hF
  letI : Nonempty F := ⟨⟨c0,hc0⟩⟩
  apply finiteAverage_probability
  intro c
  refine ⟨uniformFiniteLaw_nonneg _,uniformFiniteLaw_mass _ ?_⟩
  rw [completedBlock_card hs e i0 K hK hcol]
  exact Nat.mul_pos (Nat.zero_lt_of_lt i0.isLt) (pow_pos (by decide) s)

theorem partialMixture_source_value {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hfirst : ∀ j,K i0 j=1) (hcol : ∀ t,K t i0=1)
    (F : Finset (OffsetParameters k s i0)) (d : F) (a : Fin s → Bool) :
    partialMixture e i0 K F (sourceCode e i0 (offsetSeed (extendOffsets i0 d.val) a))=
      (1/(F.card:ℝ))*(1/((k*2^s:ℕ):ℝ)) := by
  classical
  have heq (c : F) : c.val=d.val ↔ c=d := Subtype.val_injective.eq_iff
  simp only [partialMixture,finiteAverage,
    completedBlockLaw_source_value hs e i0 K hK hfirst hcol,heq]
  simp [mul_ite]

theorem partialMixture_scaled_source {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hfirst : ∀ j,K i0 j=1) (hcol : ∀ t,K t i0=1)
    (F : Finset (OffsetParameters k s i0)) (y : SourceOutcome k s i0)
    (hy : y∈selectedOriginal e i0 F) :
    partialMixture e i0 K F y=(1/(k:ℝ))*uniformFiniteLaw (selectedOriginal e i0 F) y := by
  classical
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hy
  rw [←hp,partialMixture_source_value hs e i0 K hK hfirst hcol]
  have hm : sourceCode e i0 (offsetSeed (extendOffsets i0 p.1.val) p.2)∈selectedOriginal e i0 F :=
    Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩
  simp only [uniformFiniteLaw,hm,ite_true,selectedOriginal_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hk : (k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i0.isLt))
  have hF : (F.card:ℝ)≠0 := by exact_mod_cast (Finset.card_ne_zero.mpr ⟨p.1.val,p.1.property⟩)
  have hh : (2:ℝ)^s≠0 := pow_ne_zero s (by norm_num)
  field_simp <;> ring

theorem partialMixture_exact_distance {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hfirst : ∀ j,K i0 j=1) (hcol : ∀ t,K t i0=1)
    (F : Finset (OffsetParameters k s i0)) (hF : F.Nonempty) :
    totalVariation (uniformFiniteLaw (selectedOriginal e i0 F)) (partialMixture e i0 K F)=1-1/(k:ℝ) := by
  classical
  have hprob := partialMixture_probability hs e i0 K hK hcol F hF
  have hpos : 0<(selectedOriginal e i0 F).card := by
    rw [selectedOriginal_card]
    exact Nat.mul_pos (Finset.card_pos.mpr hF) (pow_pos (by decide) s)
  have hk : (0:ℝ)<k := by exact_mod_cast (Nat.zero_lt_of_lt i0.isLt)
  have hbeta : 1/(k:ℝ)≤1 := by
    apply (div_le_one hk).2
    exact_mod_cast (by have h := i0.isLt;omega : 1≤k)
  apply variation_of_scaled_support (selectedOriginal e i0 F) _ _ (1/(k:ℝ)) hbeta
    (uniformFiniteLaw_nonneg _) hprob.1 (uniformFiniteLaw_mass _ hpos) hprob.2
  · intro y hy
    simp [uniformFiniteLaw,hy]
  · intro y hy
    exact partialMixture_scaled_source hs e i0 K hK hfirst hcol F y hy

end
end EntropyDesigns.ConcentratedFamily
