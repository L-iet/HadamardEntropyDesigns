/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.CompletedBlocks
public import EntropySupportDistance.FiniteMixtures
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

def completionMixture {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) : SourceOutcome k s i0 → ℝ :=
  finiteAverage (fun c : OffsetParameters k s i0 => uniformFiniteLaw (completedBlock e i0 K c))

theorem completionMixture_mem {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) (hcol : ∀ t,K t i0=1) :
    completionMixture e i0 K∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) := by
  exact finiteAverage_mem_convexHull _ _ (fun c => completedBlockLaw_mem hs e i0 K hK hcol c)

theorem completionMixture_probability {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) (hcol : ∀ t,K t i0=1) :
    (∀ y,0≤completionMixture e i0 K y) ∧ ∑ y,completionMixture e i0 K y=1 := by
  apply finiteAverage_probability
  intro c
  refine ⟨uniformFiniteLaw_nonneg _,uniformFiniteLaw_mass _ ?_⟩
  rw [completedBlock_card hs e i0 K hK hcol]
  have hk : 0<k := by have h := i0.isLt;omega
  exact Nat.mul_pos hk (pow_pos (by decide) s)

theorem completionMixture_source_value {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s))
    (i0 : Fin k) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hfirst : ∀ j,K i0 j=1) (hcol : ∀ t,K t i0=1)
    (d : OffsetParameters k s i0) (a : Fin s → Bool) :
    completionMixture e i0 K (sourceCode e i0 (offsetSeed (extendOffsets i0 d) a))=
      (1/(k:ℝ))*(1/((2:ℝ)^s)^k) := by
  classical
  have he : completionMixture e i0 K (sourceCode e i0 (offsetSeed (extendOffsets i0 d) a))=
      (1/(Fintype.card (OffsetParameters k s i0):ℝ))*(1/((k*2^s:ℕ):ℝ)) := by
    simp only [completionMixture,finiteAverage,
      completedBlockLaw_source_value hs e i0 K hK hfirst hcol]
    simp [mul_ite]
  rw [he,card_offset_parameters]
  simp only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_mul]
  have hk : 1≤k := by have h := i0.isLt;omega
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast (by omega : k≠0)
  have hh0 : (2:ℝ)^s≠0 := pow_ne_zero s (by norm_num)
  have hpow : ((2:ℝ)^s)^k=((2:ℝ)^s)^(k-1)*(2:ℝ)^s := by
    conv_lhs => rw [←Nat.sub_add_cancel hk]
    rw [pow_succ]
  field_simp [hk0,hh0,hpow]
  rw [hpow]
  ring

theorem completionMixture_exact_distance {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s))
    (i0 : Fin k) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hfirst : ∀ j,K i0 j=1) (hcol : ∀ t,K t i0=1)
    (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p)
    (hsupport : sourceSupported e i0 p)
    (hweight : ∀ x : BlockSeeds k s,p (sourceCode e i0 x)=1/((2:ℝ)^s)^k) :
    totalVariation p (completionMixture e i0 K)=1-1/(k:ℝ) := by
  classical
  have hprob := completionMixture_probability hs e i0 K hK hcol
  have hk : (0:ℝ)<k := by exact_mod_cast (Nat.zero_lt_of_lt i0.isLt)
  have hbeta : 1/(k:ℝ)≤1 := by
    apply (div_le_one hk).2
    exact_mod_cast (by have h := i0.isLt;omega : 1≤k)
  apply variation_of_scaled_support (observedSupport e i0) p (completionMixture e i0 K)
    (1/(k:ℝ)) hbeta hp.1 hprob.1 hp.2.1 hprob.2
  · intro y hy
    apply hsupport y
    rintro ⟨x,hx⟩
    exact hy (Finset.mem_image.mpr ⟨x,Finset.mem_univ x,hx⟩)
  · intro y hy
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hy
    let z := (offsetPartitionEquiv (s:=s) i0).symm x
    have hx : offsetSeed (extendOffsets i0 z.1) z.2=x :=
      (offsetPartitionEquiv (s:=s) i0).apply_symm_apply x
    rw [←hx,completionMixture_source_value hs e i0 K hK hfirst hcol,hweight]

end
end EntropyDesigns.SupportFace
