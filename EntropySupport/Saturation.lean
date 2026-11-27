/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupport.Criterion
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
@[expose] public section
namespace EntropyDesigns
noncomputable section

def booleanAffineBasisLabels (r : ℕ) : Finset (Finset (Fin r)) :=
  insert ∅ (Finset.univ.image (fun i : Fin r => ({i} : Finset (Fin r))))

theorem booleanAffineBasisLabels_card (r : ℕ) :
    (booleanAffineBasisLabels r).card=r+1 := by
  classical
  have h : (∅ : Finset (Fin r))∉Finset.univ.image (fun i : Fin r => ({i} : Finset (Fin r))) := by simp
  rw [booleanAffineBasisLabels,Finset.card_insert_of_notMem h,
    Finset.card_image_of_injective _ (by intro i j h; simpa using h)]
  simp

theorem booleanAffineBasisLabels_spans (r : ℕ) :
    affineSpan (ZMod 2) (booleanSupportVector '' (booleanAffineBasisLabels r : Set (Finset (Fin r))))=⊤ := by
  classical
  let A := affineSpan (ZMod 2) (booleanSupportVector '' (booleanAffineBasisLabels r : Set (Finset (Fin r))))
  have hzero : (0 : Fin r → ZMod 2)∈A := by
    have hm : (∅ : Finset (Fin r))∈booleanAffineBasisLabels r := by simp [booleanAffineBasisLabels]
    have h := subset_affineSpan (ZMod 2) _ (Set.mem_image_of_mem booleanSupportVector hm)
    have he : booleanSupportVector (∅ : Finset (Fin r))=0 := by
      funext i; simp [booleanSupportVector]
    rw [he] at h
    exact h
  have hunit : ∀ i : Fin r,Pi.single i (1 : ZMod 2)∈A.direction := by
    intro i
    have hm : ({i} : Finset (Fin r))∈booleanAffineBasisLabels r := by simp [booleanAffineBasisLabels]
    have h := subset_affineSpan (ZMod 2) _ (Set.mem_image_of_mem booleanSupportVector hm)
    have hv := A.vsub_mem_direction h hzero
    have he : booleanSupportVector ({i} : Finset (Fin r))=Pi.single i 1 := by
      funext j; simp [booleanSupportVector,Pi.single_apply,eq_comm]
    simpa only [vsub_eq_sub,sub_zero,he] using hv
  have hd : A.direction=⊤ := by
    apply top_unique
    rw [← (Pi.basisFun (ZMod 2) (Fin r)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    simpa using hunit i
  exact (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨0,hzero⟩).mp hd

theorem affineSpanningBooleanLabels_card {r : ℕ} (T : Finset (Finset (Fin r)))
    (hspan : affineSpan (ZMod 2) (booleanSupportVector '' (T : Set (Finset (Fin r))))=⊤) :
    r+1≤T.card := by
  by_contra h
  have hc : T.card≤r := by omega
  have he : (T : Set (Finset (Fin r))).encard≤Module.finrank (ZMod 2) (Fin r → ZMod 2) := by
    simpa using (show (T.card : ENat)≤(r : ENat) by exact_mod_cast hc)
  exact (affineSpan_image_ne_top_of_encard_le_finrank (ZMod 2) T.finite_toSet he booleanSupportVector) hspan

theorem exists_affineSpanningBooleanLabels {r k : ℕ} (hlo : r+1≤k) (hhi : k≤2^r) :
    ∃ T : Finset (Finset (Fin r)),T.card=k ∧
      affineSpan (ZMod 2) (booleanSupportVector '' (T : Set (Finset (Fin r))))=⊤ := by
  classical
  obtain ⟨T,hBT,_,hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (booleanAffineBasisLabels r))
    ((booleanAffineBasisLabels_card r).trans_le hlo) (by simpa using hhi)
  refine ⟨T,hcard,?_⟩
  apply top_unique
  rw [← booleanAffineBasisLabels_spans r]
  apply affineSpan_mono (ZMod 2)
  exact Set.image_mono hBT


def HasDegreeHadamardSeedEncoding {d : ℕ}
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (r D : ℕ) : Prop :=
  ∃ labels : Fin (d+1) → Finset (Fin r),Function.Injective labels ∧
    ∃ f : Fin d → (Finset (Fin r) → ZMod 2),
      (∀ i,f i∈lowDegreeBooleanCode r D) ∧
      (∀ j i,booleanValueSign (f i (labels j))=H j i.succ)

theorem degree_sub_two_encoding_iff_complement_capacity {d r : ℕ}
    (hN : 4≤d+1) (hr : 4≤r) (hres : (d+1)%8=4) (hhi : d+1<2^r)
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H)
    (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1) :
    HasDegreeHadamardSeedEncoding H r (r-2) ↔ r+1≤2^r-(d+1) := by
  classical
  have hproper : ∀ labels : Fin (d+1) → Finset (Fin r),Function.Injective labels →
      Finset.univ.image labels≠Finset.univ := by
    intro labels hinj he
    have hc := congrArg Finset.card he
    simp only [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_finset,Fintype.card_fin] at hc
    omega
  have hrange : ∀ T : Finset (Finset (Fin r)),
      Set.range (fun z : {z : Finset (Fin r) // z∈T} => booleanSupportVector z.val)=
      booleanSupportVector '' (T : Set (Finset (Fin r))) := by
    intro T
    ext v
    constructor
    · rintro ⟨z,rfl⟩; exact ⟨z.val,z.property,rfl⟩
    · rintro ⟨z,hz,rfl⟩; exact ⟨⟨z,hz⟩,rfl⟩
  constructor
  · rintro ⟨labels,hinj,f,hf,hm⟩
    have hs := (fixed_support_hadamard_degree_criterion hN hr hres H hH hzero labels hinj (hproper labels hinj)).mp ⟨f,hf,hm⟩
    let T := (Finset.univ.image labels)ᶜ
    have he : Set.range (fun z : {z : Finset (Fin r) // z∉Finset.univ.image labels} => booleanSupportVector z.val)=
        booleanSupportVector '' (T : Set (Finset (Fin r))) := by
      ext v
      constructor
      · rintro ⟨z,rfl⟩; exact ⟨z.val,by simpa [T] using z.property,rfl⟩
      · rintro ⟨z,hz,rfl⟩; exact ⟨⟨z,by simpa [T] using hz⟩,rfl⟩
    rw [he] at hs
    have hc := affineSpanningBooleanLabels_card T hs
    simpa only [T,Finset.card_compl,Finset.card_image_of_injective _ hinj,Fintype.card_finset,Fintype.card_fin,Finset.card_univ] using hc
  · intro hc
    obtain ⟨T,hT,hspan⟩ := exists_affineSpanningBooleanLabels hc (Nat.sub_le _ _)
    let S := Tᶜ
    have hS : S.card=d+1 := by
      simp only [S,Finset.card_compl,Fintype.card_finset,Fintype.card_fin,hT]
      omega
    let e : Fin (d+1) ≃ S := Fintype.equivOfCardEq (by simp [hS])
    let labels : Fin (d+1) → Finset (Fin r) := fun j => (e j).val
    have hinj : Function.Injective labels := Subtype.val_injective.comp e.injective
    have himage : Finset.univ.image labels=S := by
      ext z
      constructor
      · rintro hz
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hz
        exact (e j).property
      · intro hz
        obtain ⟨j,hj⟩ := e.surjective ⟨z,hz⟩
        exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,congrArg Subtype.val hj⟩
    have hs : affineSpan (ZMod 2) (Set.range
        (fun z : {z : Finset (Fin r) // z∉Finset.univ.image labels} => booleanSupportVector z.val))=⊤ := by
      rw [himage]
      have he : Set.range (fun z : {z : Finset (Fin r) // z∉S} => booleanSupportVector z.val)=
          booleanSupportVector '' (T : Set (Finset (Fin r))) := by
        ext v
        constructor
        · rintro ⟨z,rfl⟩; exact ⟨z.val,by simpa [S] using z.property,rfl⟩
        · rintro ⟨z,hz,rfl⟩; exact ⟨⟨z,by simpa [S] using hz⟩,rfl⟩
      rwa [he]
    obtain ⟨f,hf,hm⟩ := (fixed_support_hadamard_degree_criterion hN hr hres H hH hzero labels hinj (hproper labels hinj)).mpr hs
    exact ⟨labels,hinj,f,hf,hm⟩


theorem prescribed_label_degree_pred_encoding {d r : ℕ} (hr : 0<r)
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H)
    (labels : Fin (d+1) → Finset (Fin r)) (hinj : Function.Injective labels)
    (hproper : Finset.univ.image labels≠Finset.univ) :
    ∃ f : Fin d → (Finset (Fin r) → ZMod 2),
      (∀ i,f i∈lowDegreeBooleanCode r (r-1)) ∧
      (∀ j i,booleanValueSign (f i (labels j))=H j i.succ) := by
  classical
  let S := Finset.univ.image labels
  have hext := properBooleanSupport_degree_pred_extension hr S hproper
  let rows := integerHadamardTruthRows H
  let v : Fin d → (S → ZMod 2) := fun i z =>
    binaryObservationMatrix rows (Function.invFun labels z.val) i
  choose f hf he using fun i => hext (v i)
  refine ⟨f,hf,?_⟩
  intro j i
  have hz : labels j∈S := Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  have hh := congrFun (he i) ⟨labels j,hz⟩
  change f i (labels j)=binaryObservationMatrix rows (Function.invFun labels (labels j)) i at hh
  rw [Function.leftInverse_invFun hinj j] at hh
  rw [hh]
  exact integerHadamardTruthRows_binary_value hH j i

theorem degree_pred_encoding_exists {d r : ℕ} (hr : 0<r) (hhi : d+1<2^r)
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H) :
    HasDegreeHadamardSeedEncoding H r (r-1) := by
  classical
  obtain ⟨e : Fin (d+1) ↪ Finset (Fin r)⟩ := Function.Embedding.nonempty_of_card_le (α:=Fin (d+1)) (β:=Finset (Fin r))
    (by simpa only [Fintype.card_fin,Fintype.card_finset] using hhi.le)
  have hp : Finset.univ.image e≠Finset.univ := by
    intro he
    have hc := congrArg Finset.card he
    simp only [Finset.card_image_of_injective _ e.injective,Finset.card_univ,Fintype.card_finset,Fintype.card_fin] at hc
    omega
  obtain ⟨f,hf,hm⟩ := prescribed_label_degree_pred_encoding hr H hH e e.injective hp
  exact ⟨e,e.injective,f,hf,hm⟩

theorem degree_encoding_mono {d r D E : ℕ}
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hDE : D≤E)
    (h : HasDegreeHadamardSeedEncoding H r D) : HasDegreeHadamardSeedEncoding H r E := by
  obtain ⟨labels,hinj,f,hf,hm⟩ := h
  refine ⟨labels,hinj,f,?_,hm⟩
  intro i
  apply (Submodule.span_mono ?_) (hf i)
  rintro _ ⟨z,rfl⟩
  exact ⟨⟨z.val,z.property.trans hDE⟩,rfl⟩

theorem minimal_seed_degree_saturation {d r : ℕ}
    (hN : 4≤d+1) (hr : 4≤r) (hres : (d+1)%8=4)
    (hlo : 2^(r-1)<d+1) (hhi : d+1<2^r)
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H)
    (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1) :
    (HasDegreeHadamardSeedEncoding H r (r-2) ↔ r+1≤2^r-(d+1)) ∧
    (2^r-(d+1)≤r → HasDegreeHadamardSeedEncoding H r (r-1) ∧
      ∀ D,HasDegreeHadamardSeedEncoding H r D → r-1≤D) := by
  have hc := degree_sub_two_encoding_iff_complement_capacity hN hr hres hhi H hH hzero
  refine ⟨hc,?_⟩
  intro hgap
  refine ⟨degree_pred_encoding_exists (by omega) hhi H hH,?_⟩
  intro D hD
  by_contra h
  have he : HasDegreeHadamardSeedEncoding H r (r-2) := degree_encoding_mono H (by omega) hD
  have := hc.mp he
  omega

theorem four_omitted_labels_degree_exact {d r : ℕ}
    (hr : 4≤r) (horder : d+1=2^r-4)
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H)
    (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1) :
    HasDegreeHadamardSeedEncoding H r (r-1) ∧
      ∀ D,HasDegreeHadamardSeedEncoding H r D → r-1≤D := by
  have hpow : 16≤2^r := by exact (Nat.pow_le_pow_right (by omega : 1≤2) hr)
  have hprev : 8≤2^(r-1) := by
    have hh : 3≤r-1 := by omega
    exact Nat.pow_le_pow_right (by omega : 1≤2) hh
  have he : 2^r=2*2^(r-1) := by
    conv_lhs => rw [show r=(r-1)+1 by omega,pow_succ]
    omega
  have hdiv : 8∣2^r := by
    have he : r=3+(r-3) := by omega
    rw [he,pow_add]
    exact dvd_mul_right 8 _
  have hres : (d+1)%8=4 := by
    have hh := Nat.mod_eq_zero_of_dvd hdiv
    omega
  have hs := minimal_seed_degree_saturation (d:=d) (r:=r) (by omega) hr hres
    (by omega) (by omega) H hH hzero
  exact hs.2 (by omega)

end
end EntropyDesigns
