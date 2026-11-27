/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SelectedEndpoint
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section

theorem finite_sets_matching {A : Type*} [DecidableEq A] (S T : Finset A) (hcard : S.card=T.card) :
    ∃ E : {x // x∈S} ≃ {y // y∈T},∀ x,(E x).val=x.val ↔ x.val∈T := by
  classical
  have hc : Fintype.card {x // x∈S\T}=Fintype.card {y // y∈T\S} := by
    simp only [Fintype.card_coe,Finset.card_sdiff]
    rw [hcard,Finset.inter_comm]
  let D : {x // x∈S\T} ≃ {y // y∈T\S} := Fintype.equivOfCardEq hc
  let f : {x // x∈S} → {y // y∈T} := fun x =>
    if h : x.val∈T then ⟨x.val,h⟩ else
      ⟨(D ⟨x.val,Finset.mem_sdiff.mpr ⟨x.property,h⟩⟩).val,
        (Finset.mem_sdiff.mp (D ⟨x.val,Finset.mem_sdiff.mpr ⟨x.property,h⟩⟩).property).1⟩
  have hkeep (x : {x // x∈S}) (hx : x.val∈T) : (f x).val=x.val := by simp [f,hx]
  have hnew (x : {x // x∈S}) (hx : x.val∉T) : (f x).val∉S := by
    simp only [f,hx,dif_neg]
    exact (Finset.mem_sdiff.mp (D ⟨x.val,Finset.mem_sdiff.mpr ⟨x.property,hx⟩⟩).property).2
  have hinj : Function.Injective f := by
    intro x y heq
    have hv := congrArg Subtype.val heq
    by_cases hx : x.val∈T
    · by_cases hy : y.val∈T
      · apply Subtype.ext
        simpa only [hkeep x hx,hkeep y hy] using hv
      · have hn := hnew y hy
        have he : (f y).val=x.val := hv.symm.trans (hkeep x hx)
        rw [he] at hn
        exact False.elim (hn x.property)
    · by_cases hy : y.val∈T
      · have hn := hnew x hx
        have he : (f x).val=y.val := hv.trans (hkeep y hy)
        rw [he] at hn
        exact False.elim (hn y.property)
      · simp only [f,hx,hy,dif_neg] at hv
        have hd := D.injective (Subtype.ext hv)
        exact Subtype.ext (congrArg (fun z : {x // x∈S\T} => z.val) hd)
  have hsurj : Function.Surjective f := by
    intro y
    by_cases hy : y.val∈S
    · refine ⟨⟨y.val,hy⟩,?_⟩
      apply Subtype.ext
      exact hkeep ⟨y.val,hy⟩ y.property
    · let v : {y // y∈T\S} := ⟨y.val,Finset.mem_sdiff.mpr ⟨y.property,hy⟩⟩
      let u := D.symm v
      have hu := Finset.mem_sdiff.mp u.property
      refine ⟨⟨u.val,hu.1⟩,?_⟩
      apply Subtype.ext
      simpa [f,hu.2,u,v] using
        (congrArg (fun z : {y // y∈T\S} => z.val) (D.apply_symm_apply v))
  refine ⟨Equiv.ofBijective f ⟨hinj,hsurj⟩,?_⟩
  intro x
  change (f x).val=x.val ↔ x.val∈T
  constructor
  · intro heq
    by_contra hx
    have hn := hnew x hx
    rw [heq] at hn
    exact hn x.property
  · exact hkeep x

end
end EntropyDesigns.SupportFace
