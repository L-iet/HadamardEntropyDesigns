/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySeedRepair.CardinalityRepair
public import EntropySeedRepair.BooleanLabels
public import EntropySeedRepair.ExchangePaths
@[expose] public section
namespace EntropyDesigns.SupportRepair
noncomputable section
set_option backward.isDefEq.respectTransparency false

def labelAffineCodimension {r : ℕ} (T : Finset (Finset (Fin r))) : ℕ :=
  r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (booleanSupportVector '' (T : Set (Finset (Fin r)))))

theorem boolean_support_repair_at_codimension {r : ℕ} (T : Finset (Finset (Fin r)))
    (hcard : r+1≤T.card) :
    ∃ U : Finset (Finset (Fin r)),U.card=T.card ∧
      affineSpan (ZMod 2) (booleanSupportVector '' (U : Set (Finset (Fin r))))=⊤ ∧
      SupportExchangePath (labelAffineCodimension T) T U := by
  classical
  let e := booleanLabelsEquiv r
  let V := T.map e.toEmbedding
  have hVcard : r+1≤V.card := by simpa [V] using hcard
  obtain ⟨W,hWcard,hWspan,hWdiff⟩ := exact_affine_spanning_repair V hVcard
  let U := W.map e.symm.toEmbedding
  have hforward : U.map e.toEmbedding=W := by
    ext v
    simp [U,Finset.mem_map_equiv]
  have hUcard : U.card=T.card := by simpa [U,V] using hWcard
  have hUspan : affineSpan (ZMod 2) (booleanSupportVector '' (U : Set (Finset (Fin r))))=⊤ := by
    rw [←boolean_label_image_as_vectors U]
    rw [hforward]
    exact hWspan
  have hdiff : (T\U).map e.toEmbedding=V\W := by
    rw [Finset.map_sdiff,hforward]
  have hdiffcard : (T\U).card=(V\W).card := by
    simpa only [Finset.card_map] using congrArg Finset.card hdiff
  have hVcoe : (V : Set (Fin r → ZMod 2))=booleanSupportVector '' (T : Set (Finset (Fin r))) :=
    boolean_label_image_as_vectors T
  have hdim : (V\W).card=labelAffineCodimension T := by
    change (V\W).card=r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (booleanSupportVector '' (T : Set (Finset (Fin r)))))
    rw [←hVcoe]
    exact hWdiff
  have hp := exists_shortest_exchange_path T U hUcard.symm
  rw [hdiffcard,hdim] at hp
  exact ⟨U,hUcard,hUspan,hp⟩

theorem boolean_support_exchange_lower {r k : ℕ} (T U : Finset (Finset (Fin r)))
    (hcard : r+1≤T.card) (hpath : SupportExchangePath k T U)
    (hspan : affineSpan (ZMod 2) (booleanSupportVector '' (U : Set (Finset (Fin r))))=⊤) :
    labelAffineCodimension T≤k := by
  classical
  let e := booleanLabelsEquiv r
  let V := T.map e.toEmbedding
  let W := U.map e.toEmbedding
  have hTcard := exchange_path_preserves_card T U hpath
  have hV : V.Nonempty := Finset.card_pos.mp (by simpa [V] using (show 0<T.card by omega))
  have hVW : W.card=V.card := by simpa [W,V] using hTcard
  have hWspan : affineSpan (ZMod 2) (W : Set (Fin r → ZMod 2))=⊤ := by
    simpa only [W,e,boolean_label_image_as_vectors] using hspan
  have hdiff : (V\W).card=(T\U).card := by
    dsimp [V,W]
    rw [←Finset.map_sdiff,Finset.card_map]
  have hl := affine_spanning_repair_lower V W hV hVW hWspan
  have hVcoe : (V : Set (Fin r → ZMod 2))=booleanSupportVector '' (T : Set (Finset (Fin r))) :=
    boolean_label_image_as_vectors T
  have hl' : labelAffineCodimension T≤(T\U).card := by
    change r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (booleanSupportVector '' (T : Set (Finset (Fin r)))))≤(T\U).card
    rw [←hVcoe,←hdiff]
    exact hl
  exact hl'.trans (exchange_path_difference_bound T U hpath)

end
end EntropyDesigns.SupportRepair
