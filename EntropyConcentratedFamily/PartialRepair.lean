/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SelectedRepair
@[expose] public section
set_option maxHeartbeats 2000000
namespace EntropyDesigns.ConcentratedFamily
noncomputable section
open SupportFace

theorem selectedOriginal_mono {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    {F G : Finset (OffsetParameters k s i0)} (hFG : F⊆G) :
    selectedOriginal e i0 F⊆selectedOriginal e i0 G := by
  classical
  intro y hy
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr ⟨(⟨p.1.val,hFG p.1.property⟩,p.2),Finset.mem_univ _,rfl⟩

theorem selectedOriginal_subset_source {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (F : Finset (OffsetParameters k s i0)) : selectedOriginal e i0 F⊆observedSupport e i0 := by
  classical
  intro y hy
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr ⟨offsetSeed (extendOffsets i0 p.1.val) p.2,Finset.mem_univ _,rfl⟩

theorem partial_source_intersection {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hfirst : ∀ j,K i0 j=1) (hcol : ∀ t,K t i0=1)
    (F G : Finset (OffsetParameters k s i0)) (hGF : G⊆F) :
    selectedOriginal e i0 F∩selectedEndpoint e i0 K G=selectedOriginal e i0 G := by
  classical
  have hfull := selectedEndpoint_source_intersection hs e i0 K hK hfirst hcol G
  ext y
  constructor
  · intro hy
    have hh := Finset.mem_inter.mp hy
    rw [←hfull]
    exact Finset.mem_inter.mpr ⟨selectedOriginal_subset_source e i0 F hh.1,hh.2⟩
  · intro hy
    have hg := hy
    rw [←hfull] at hg
    exact Finset.mem_inter.mpr ⟨selectedOriginal_mono e i0 hGF hy,(Finset.mem_inter.mp hg).2⟩

theorem partial_collision_preserving_repair {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hfirst : ∀ j,K i0 j=1) (hcol : ∀ t,K t i0=1)
    (F : Finset (OffsetParameters k s i0)) (hF : F.Nonempty) (hdiv : k∣F.card) :
    ∃ G : Finset (OffsetParameters k s i0),G⊆F ∧ G.card=F.card/k ∧
      (selectedEndpoint e i0 K G).card=F.card*2^s ∧
      (selectedOriginal e i0 F∩selectedEndpoint e i0 K G).card=(F.card*2^s)/k ∧
      (∀ c∈G,Matrix.IsHadamard (offsetHadamard e i0 (extendOffsets i0 c) K)) ∧
      selectedEndpoint e i0 K G=G.biUnion (completedBlock e i0 K) ∧
      (∃ E : {x // x∈selectedOriginal e i0 F} ≃ {y // y∈selectedEndpoint e i0 K G},
        (∀ x,(E x).val=x.val ↔ x.val∈selectedEndpoint e i0 K G) ∧
        Fintype.card {x : {x // x∈selectedOriginal e i0 F} // (E x).val≠x.val}=
          F.card*2^s-(F.card*2^s)/k ∧
        ((Fintype.card {x : {x // x∈selectedOriginal e i0 F} // (E x).val≠x.val}:ℕ):ℝ)=
          ((F.card*2^s:ℕ):ℝ)*(1-1/(k:ℝ))) ∧
      collision (uniformFiniteLaw (selectedOriginal e i0 F))=1/((F.card*2^s:ℕ):ℝ) ∧
      collision (uniformFiniteLaw (selectedEndpoint e i0 K G))=1/((F.card*2^s:ℕ):ℝ) := by
  classical
  let b := F.card/k
  let D := F.card*2^s
  obtain ⟨G,hGF,hG⟩ := Finset.exists_subset_card_eq (Nat.div_le_self F.card k)
  have hmul : k*b=F.card := Nat.mul_div_cancel' hdiv
  have hD : D=k*(b*2^s) := by
    calc
      D=(k*b)*2^s := congrArg (fun z : ℕ => z*2^s) hmul.symm
      _=k*(b*2^s) := by ring
  have hk0 : k≠0 := Nat.ne_of_gt (Nat.zero_lt_of_lt i0.isLt)
  have hDquot : D/k=b*2^s := by rw [hD];simp [hk0]
  have hS : (selectedOriginal e i0 F).card=D := selectedOriginal_card e i0 F
  have hT : (selectedEndpoint e i0 K G).card=D := by
    rw [selectedEndpoint_card hs e i0 K hK hcol,hG]
    change b*(k*2^s)=D
    rw [hD]
    ring
  have hI : (selectedOriginal e i0 F∩selectedEndpoint e i0 K G).card=D/k := by
    rw [partial_source_intersection hs e i0 K hK hfirst hcol F G hGF,selectedOriginal_card,hG,hDquot]
  obtain ⟨E,hfix,hchanged⟩ := finite_sets_exact_replacements
    (selectedOriginal e i0 F) (selectedEndpoint e i0 K G) (hS.trans hT.symm)
  rw [hS,hI] at hchanged
  have hret : b*2^s≤D := by rw [←hDquot];exact Nat.div_le_self _ _
  have hDr : (D:ℝ)=(k:ℝ)*((b*2^s:ℕ):ℝ) := by exact_mod_cast hD
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk0
  have hexact : ((Fintype.card {x : {x // x∈selectedOriginal e i0 F} // (E x).val≠x.val}:ℕ):ℝ)=
      (D:ℝ)*(1-1/(k:ℝ)) := by
    rw [hchanged,hDquot,Nat.cast_sub hret]
    field_simp [hkR]
    nlinarith [hDr]
  have hDpos : 0<D := Nat.mul_pos (Finset.card_pos.mpr hF) (pow_pos (by decide) s)
  refine ⟨G,hGF,hG,hT,hI,(fun c _ => offsetHadamard_isHadamard e i0 (extendOffsets i0 c) K hK),
    selectedEndpoint_union e i0 K G,⟨E,hfix,hchanged,hexact⟩,?_,?_⟩
  · rw [uniformFiniteLaw_collision _ (by rw [hS];exact hDpos),hS]
  · rw [uniformFiniteLaw_collision _ (by rw [hT];exact hDpos),hT]

end
end EntropyDesigns.ConcentratedFamily
