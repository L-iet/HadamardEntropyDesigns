/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Sound coloring and vertex-branch rules for finite clique certificates. -/
module
public import EntropyQuadraticClassification.OrbitCliqueBasics
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Finset.Range
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
variable {V : Type*} [DecidableEq V]

theorem cliqueBound_coloring {R : V → V → Prop} (S : Finset V)
    (b : ℕ) (color : V → ℕ) (hc : ∀ x∈S,color x<b)
    (hproper : ∀ x∈S,∀ y∈S,R x y → color x≠color y) :
    ListCliqueBound R S b := by
  intro L hL hp
  have hn : (L.map color).Nodup := List.pairwise_map.mpr
    (List.Pairwise.imp_of_mem
      (fun {a b} ha hb hab => hproper a (hL a ha) b (hL b hb) hab) hp)
  have hsub : (L.map color).toFinset⊆Finset.range b := by
    intro c hh
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hh)
    exact Finset.mem_range.mpr (hc x (hL x hx))
  have hb := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn,List.length_map,Finset.card_range] at hb
  exact hb

theorem cliqueBound_vertex_branch {R : V → V → Prop} [DecidableRel R]
    (hSymm : ∀ {x y : V},R x y → R y x) (S : Finset V) (v : V) (b : ℕ)
    (htail : ListCliqueBound R (S.erase v) (b+1))
    (hneighbors : ListCliqueBound R (S.filter (R v)) b) :
    ListCliqueBound R S (b+1) := by
  intro L hL hp
  by_cases hv : v∈L
  · have hperm := List.perm_cons_erase hv
    have hpc : (v::L.erase v).Pairwise R := (hperm.pairwise_iff hSymm).mp hp
    obtain ⟨hhead,htailPair⟩ := List.pairwise_cons.mp hpc
    have hmem : ∀ z∈L.erase v,z∈S.filter (R v) := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨hL z (List.mem_of_mem_erase hz),hhead z hz⟩
    have hb := hneighbors (L.erase v) hmem htailPair
    have hlen := List.length_erase_add_one hv
    omega
  · apply htail L ?_ hp
    intro z hz
    apply Finset.mem_erase.mpr
    refine ⟨?_,hL z hz⟩
    intro he
    subst z
    exact hv hz

end EntropyDesigns.QuadraticRefinement
