/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySeedRepair.BasisSubset
@[expose] public section
namespace EntropyDesigns.SupportRepair
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem exact_affine_spanning_repair {r : ℕ} (T : Finset (Fin r → ZMod 2))
    (hcard : r+1≤T.card) :
    ∃ U : Finset (Fin r → ZMod 2),U.card=T.card ∧
      affineSpan (ZMod 2) (U : Set (Fin r → ZMod 2))=⊤ ∧
      (T\U).card=r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (T : Set (Fin r → ZMod 2))) := by
  classical
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨B,hBT,hBi,hBspan,hBcard⟩ := finite_affine_basis_subset T hT
  obtain ⟨A,hBA,hAi,hAspan,hAcard⟩ := finite_full_affine_basis_extension B hBi
  let d := Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (T : Set (Fin r → ZMod 2)))
  have hd : d≤r := by simpa [d] using Submodule.finrank_le (vectorSpan (ZMod 2) (T : Set (Fin r → ZMod 2)))
  let L := A\B
  have hLcard : L.card=r-d := by
    rw [Finset.card_sdiff_of_subset hBA,hAcard,hBcard]
    change r+1-(d+1)=r-d
    omega
  have hdis : Disjoint T L := by
    apply Finset.disjoint_left.mpr
    intro x hxT hxL
    obtain ⟨hxA,hxnotB⟩ := Finset.mem_sdiff.mp hxL
    apply hxnotB
    have hxspan : x∈affineSpan (ZMod 2) (B : Set (Fin r → ZMod 2)) := by
      rw [hBspan]
      exact mem_affineSpan (ZMod 2) hxT
    exact independent_span_intersection (A : Set (Fin r → ZMod 2))
      (B : Set (Fin r → ZMod 2)) hBA hAi x hxA hxspan
  have hroom : r-d≤(T\B).card := by
    rw [Finset.card_sdiff_of_subset hBT,hBcard]
    change r-d≤T.card-(d+1)
    omega
  obtain ⟨R,hRsub,hRcard⟩ := Finset.exists_subset_card_eq hroom
  have hRT : R⊆T := hRsub.trans Finset.sdiff_subset
  let U := (T\R)∪L
  have hdis' : Disjoint (T\R) L := by
    apply Finset.disjoint_left.mpr
    intro x hx hxL
    exact Finset.disjoint_left.mp hdis (Finset.mem_sdiff.mp hx).1 hxL
  have hUcard : U.card=T.card := by
    rw [Finset.card_union_of_disjoint hdis',Finset.card_sdiff_of_subset hRT,hRcard,hLcard]
    omega
  have hAU : A⊆U := by
    intro x hxA
    by_cases hxB : x∈B
    · apply Finset.mem_union_left
      refine Finset.mem_sdiff.mpr ⟨hBT hxB,?_⟩
      intro hxR
      exact (Finset.mem_sdiff.mp (hRsub hxR)).2 hxB
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxA,hxB⟩)
  have hUspan : affineSpan (ZMod 2) (U : Set (Fin r → ZMod 2))=⊤ := by
    have hh := affineSpan_mono (ZMod 2) (show (A : Set (Fin r → ZMod 2))⊆U from hAU)
    rw [hAspan] at hh
    exact top_unique hh
  have hremoved : T\U=R := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxT,hxnotU⟩ := Finset.mem_sdiff.mp hx
      by_contra hxnotR
      exact hxnotU (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxT,hxnotR⟩))
    · intro hxR
      have hxT := hRT hxR
      refine Finset.mem_sdiff.mpr ⟨hxT,?_⟩
      intro hxU
      rcases Finset.mem_union.mp hxU with hxremain|hxL
      · exact (Finset.mem_sdiff.mp hxremain).2 hxR
      · exact Finset.disjoint_left.mp hdis hxT hxL
  refine ⟨U,hUcard,hUspan,?_⟩
  rw [hremoved,hRcard]

theorem affine_spanning_repair_lower {r : ℕ} (T U : Finset (Fin r → ZMod 2))
    (hT : T.Nonempty) (hcard : U.card=T.card)
    (hUspan : affineSpan (ZMod 2) (U : Set (Fin r → ZMod 2))=⊤) :
    r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (T : Set (Fin r → ZMod 2)))≤(T\U).card := by
  classical
  obtain ⟨B,hBT,_,hBspan,hBcard⟩ := finite_affine_basis_subset T hT
  let L := B∪(U\T)
  have hLspan : affineSpan (ZMod 2) (L : Set (Fin r → ZMod 2))=⊤ := by
    have hu : (U : Set (Fin r → ZMod 2))⊆affineSpan (ZMod 2) (L : Set (Fin r → ZMod 2)) := by
      intro x hxU
      by_cases hxT : x∈T
      · have hxB : x∈affineSpan (ZMod 2) (B : Set (Fin r → ZMod 2)) := by
          rw [hBspan]
          exact mem_affineSpan (ZMod 2) hxT
        exact affineSpan_mono (ZMod 2) (show (B : Set (Fin r → ZMod 2))⊆L from Finset.subset_union_left) hxB
      · exact mem_affineSpan (ZMod 2) (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxU,hxT⟩))
    have hh : affineSpan (ZMod 2) (U : Set (Fin r → ZMod 2))≤
        affineSpan (ZMod 2) (L : Set (Fin r → ZMod 2)) := (affineSpan_le).mpr hu
    rw [hUspan] at hh
    exact top_unique hh
  have hLcard : r+1≤L.card := by
    by_contra! hc
    have hcle : L.card≤r := by omega
    have henc : (L : Set (Fin r → ZMod 2)).encard≤Module.finrank (ZMod 2) (Fin r → ZMod 2) := by
      simpa using (show (L.card : ENat)≤(r : ENat) by exact_mod_cast hcle)
    have hn := affineSpan_image_ne_top_of_encard_le_finrank (ZMod 2) L.finite_toSet henc (fun x => x)
    exact hn (by simpa using hLspan)
  have hdis : Disjoint B (U\T) := by
    apply Finset.disjoint_left.mpr
    intro x hxB hxUT
    exact (Finset.mem_sdiff.mp hxUT).2 (hBT hxB)
  have he : L.card=B.card+(U\T).card := Finset.card_union_of_disjoint hdis
  have hdiff : (U\T).card=(T\U).card := by
    simp only [Finset.card_sdiff,hcard,Finset.inter_comm]
  rw [he,hBcard,hdiff] at hLcard
  omega

end
end EntropyDesigns.SupportRepair
