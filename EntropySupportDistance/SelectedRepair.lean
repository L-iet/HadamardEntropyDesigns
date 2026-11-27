/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.MatchingCount
public import EntropySupportDistance.RepairArithmetic
public import EntropySupportDistance.UniformSourceIdentity
@[expose] public section
set_option maxHeartbeats 2000000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

theorem selectedEndpoint_union {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (F : Finset (OffsetParameters k s i0)) :
    selectedEndpoint e i0 K F=F.biUnion (completedBlock e i0 K) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hy
    exact Finset.mem_biUnion.mpr ⟨p.1.val,p.1.property,
      Finset.mem_image.mpr ⟨p.2,Finset.mem_univ _,hp⟩⟩
  · intro hy
    obtain ⟨c,hc,hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨(⟨c,hc⟩,r),Finset.mem_univ _,hr⟩

theorem collision_preserving_exact_repair {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k) :
    ∃ K : Matrix (Fin k) (Fin k) ℤ,∃ F : Finset (OffsetParameters k s i0),
      Matrix.IsHadamard K ∧ (∀ j,K i0 j=1) ∧ (∀ t,K t i0=1) ∧
      F.card=(2^s)^k/(k*2^s) ∧
      sourceFeasible i0 (uniformFiniteLaw (observedSupport e i0)) ∧
      (selectedEndpoint e i0 K F).card=(2^s)^k ∧
      (observedSupport e i0∩selectedEndpoint e i0 K F).card=(2^s)^k/k ∧
      (∀ c∈F,Matrix.IsHadamard (offsetHadamard e i0 (extendOffsets i0 c) K)) ∧
      selectedEndpoint e i0 K F=F.biUnion (completedBlock e i0 K) ∧
      (∃ E : {x // x∈observedSupport e i0} ≃ {y // y∈selectedEndpoint e i0 K F},
        (∀ x,(E x).val=x.val ↔ x.val∈selectedEndpoint e i0 K F) ∧
        Fintype.card {x : {x // x∈observedSupport e i0} // (E x).val≠x.val}=
          (2^s)^k-(2^s)^k/k ∧
        ((Fintype.card {x : {x // x∈observedSupport e i0} // (E x).val≠x.val}:ℕ):ℝ)=
          (((2^s)^k:ℕ):ℝ)*(1-1/(k:ℝ))) ∧
      collision (uniformFiniteLaw (observedSupport e i0))=1/(((2^s)^k:ℕ):ℝ) ∧
      collision (uniformFiniteLaw (selectedEndpoint e i0 K F))=1/(((2^s)^k:ℕ):ℝ) := by
  classical
  have hkh : k≤2^s := by omega
  have hs : 2≤s := by
    by_contra h
    have h01 : s=0 ∨ s=1 := by omega
    rcases h01 with h0|h1
    · subst s;norm_num at hsize;omega
    · subst s;norm_num at hsize;omega
  obtain ⟨K,hK,hfirst,hcol⟩ := normalized_walsh_exists r hkpow i0
  let b := (2^s)^(k-1)/k
  let D := (2^s)^k
  obtain ⟨hbudget,hquot,hle⟩ := repair_exact_block_budget hk r hkpow hsize
  have hselect : b≤(Finset.univ : Finset (OffsetParameters k s i0)).card := by
    simpa only [Finset.card_univ,card_offset_parameters] using hle
  obtain ⟨F,_,hF⟩ := Finset.exists_subset_card_eq hselect
  have hS : (observedSupport e i0).card=D := by
    rw [observedSupport,Finset.card_image_of_injective _ (sourceCode_injective e i0)]
    simp [BlockSeeds,D]
  have hT : (selectedEndpoint e i0 K F).card=D := by
    rw [selectedEndpoint_card hs e i0 K hK hcol,hF,Nat.mul_comm]
    exact hbudget
  have hD : D=k*(b*2^s) := by
    calc
      D=(k*2^s)*b := hbudget.symm
      _=k*(b*2^s) := by ring
  have hk0 : k≠0 := by omega
  have hDquot : D/k=b*2^s := by rw [hD];simp [hk0]
  have hI : (observedSupport e i0∩selectedEndpoint e i0 K F).card=D/k := by
    rw [selectedEndpoint_source_intersection hs e i0 K hK hfirst hcol,
      selectedOriginal_card,hF,hDquot]
  obtain ⟨E,hfix,hchanged⟩ := finite_sets_exact_replacements
    (observedSupport e i0) (selectedEndpoint e i0 K F) (hS.trans hT.symm)
  rw [hS,hI] at hchanged
  have hret : b*2^s≤D := by rw [←hDquot];exact Nat.div_le_self _ _
  have hDr : (D:ℝ)=(k:ℝ)*((b*2^s:ℕ):ℝ) := by exact_mod_cast hD
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk0
  have hexact : ((Fintype.card {x : {x // x∈observedSupport e i0} // (E x).val≠x.val}:ℕ):ℝ)=
      (D:ℝ)*(1-1/(k:ℝ)) := by
    rw [hchanged,hDquot,Nat.cast_sub hret]
    field_simp [hkR]
    nlinarith [hDr]
  have hDpos : 0<D := pow_pos (pow_pos (by decide) s) k
  refine ⟨K,F,hK,hfirst,hcol,?_,uniform_observed_source_feasible hk hkh e he i0,
    hT,hI,(fun c _ => offsetHadamard_isHadamard e i0 (extendOffsets i0 c) K hK),
    selectedEndpoint_union e i0 K F,⟨E,hfix,hchanged,hexact⟩,?_,?_⟩
  · exact hF.trans hquot.symm
  · rw [uniformFiniteLaw_collision _ (by rw [hS];exact hDpos),hS]
  · rw [uniformFiniteLaw_collision _ (by rw [hT];exact hDpos),hT]

end
end EntropyDesigns.SupportFace
