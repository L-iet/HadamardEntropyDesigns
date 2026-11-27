/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Constant weight eight severely restricts binary checks on twelve labels. -/
module
public import EntropyQuadraticClassification.BinarySupports
public import EntropyQuadraticClassification.ParityPartitions
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped symmDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem third_weight_eight_support (H M N : Finset ι)
    (hcover : M ∪ N=Finset.univ) (hH : H.card=8)
    (hHM : (H ∩ M).card=4) (hHN : (H ∩ N).card=4)
    (hX : (M ∆ N).card=8) : H=M ∆ N := by
  have hUnion : (H ∩ M) ∪ (H ∩ N)=H := by
    ext x
    have hx : x∈M ∨ x∈N := by
      have hx' : x∈M ∪ N := by rw [hcover]; exact Finset.mem_univ x
      exact Finset.mem_union.mp hx'
    simp only [Finset.mem_union,Finset.mem_inter]
    tauto
  have hcard := Finset.card_union_add_card_inter (H ∩ M) (H ∩ N)
  have hz : ((H ∩ M) ∩ (H ∩ N)).card=0 := by
    rw [hUnion,hH,hHM,hHN] at hcard
    omega
  have hempty := Finset.card_eq_zero.mp hz
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    have hnot : ¬(x∈M ∧ x∈N) := by
      intro hh
      have ht : x∈(H ∩ M) ∩ (H ∩ N) := by simp [hx,hh.1,hh.2]
      rw [hempty] at ht
      simpa using ht
    have hcov : x∈M ∨ x∈N := by
      have hx' : x∈M ∪ N := by rw [hcover]; exact Finset.mem_univ x
      exact Finset.mem_union.mp hx'
    simp only [Finset.mem_symmDiff]
    tauto
  · omega

theorem constant_weight_pair_intersection
    (D : Submodule (ZMod 2) (ι → ZMod 2))
    (hw : ∀ f∈D,f≠0 → (oneSupport f).card=8)
    {f g : ι → ZMod 2} (hf : f∈D) (hg : g∈D)
    (hf0 : f≠0) (hg0 : g≠0) (hfg : f≠g) :
    (oneSupport f ∩ oneSupport g).card=4 := by
  apply weight_eight_intersection _ _ (hw f hf hf0) (hw g hg hg0)
  rw [←oneSupport_add]
  exact hw (f+g) (D.add_mem hf hg)
    (fun h => hfg ((binary_add_eq_zero_iff f g).mp h))

theorem constant_weight_four_words (hι : Fintype.card ι=12)
    (D : Submodule (ZMod 2) (ι → ZMod 2))
    (hw : ∀ f∈D,f≠0 → (oneSupport f).card=8)
    {h g : ι → ZMod 2} (hh : h∈D) (hg : g∈D)
    (hh0 : h≠0) (hg0 : g≠0) (hhg : h≠g) :
    ∀ f∈D,f=0 ∨ f=h ∨ f=g ∨ f=h+g := by
  intro f hf
  by_cases hf0 : f=0
  · exact Or.inl hf0
  by_cases hfh : f=h
  · exact Or.inr (Or.inl hfh)
  by_cases hfg : f=g
  · exact Or.inr (Or.inr (Or.inl hfg))
  have hX : (oneSupport h ∆ oneSupport g).card=8 := by
    rw [←oneSupport_add]
    exact hw _ (D.add_mem hh hg)
      (fun he => hhg ((binary_add_eq_zero_iff h g).mp he))
  have hcover := weight_eight_covers hι _ _ (hw _ hh hh0) (hw _ hg hg0) hX
  have hs := third_weight_eight_support (oneSupport f) (oneSupport h) (oneSupport g)
    hcover (hw _ hf hf0)
    (constant_weight_pair_intersection D hw hf hh hf0 hh0 hfh)
    (constant_weight_pair_intersection D hw hf hg hf0 hg0 hfg) hX
  rw [←oneSupport_add] at hs
  exact Or.inr (Or.inr (Or.inr (oneSupport_injective hs)))

end EntropyDesigns.QuadraticRefinement
