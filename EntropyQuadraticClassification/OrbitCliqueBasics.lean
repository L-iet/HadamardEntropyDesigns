/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Generic soundness rule for finite orbit-based clique upper bounds. -/
module
public import Mathlib.Data.Finset.Card
public import Init.Data.List.Pairwise
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
variable {V : Type*} [DecidableEq V]

def ListCliqueBound (R : V → V → Prop) (S : Finset V) (b : ℕ) : Prop :=
  ∀ L : List V,(∀ x∈L,x∈S) → L.Pairwise R → L.length≤b

def HasOrbitMaps (R : V → V → Prop) (S A : Finset V) : Prop :=
  ∀ x∈S,(∃ y∈S,R x y) → ∃ a∈A,∃ f : V → V,
    f x=a ∧ (∀ z∈S,f z∈S) ∧
      (∀ u∈S,∀ v∈S,R u v → R (f u) (f v))

theorem cliqueBound_mono {R : V → V → Prop} {S : Finset V} {b c : ℕ}
    (h : ListCliqueBound R S b) (hbc : b≤c) : ListCliqueBound R S c := by
  intro L hL hp
  exact (h L hL hp).trans hbc

theorem pairwise_map_on {R : V → V → Prop} (S : Finset V) (f : V → V)
    (L : List V) (hL : ∀ x∈L,x∈S)
    (hf : ∀ u∈S,∀ v∈S,R u v → R (f u) (f v)) (hp : L.Pairwise R) :
    (L.map f).Pairwise R := by
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp_of_mem
    (fun {a b} ha hb hab => hf a (hL a ha) b (hL b hb) hab) hp

theorem cliqueBound_no_edges {R : V → V → Prop} (S : Finset V)
    (hNo : ∀ x∈S,∀ y∈S,¬R x y) : ListCliqueBound R S 1 := by
  intro L hL hp
  cases L with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y ys =>
      have hxy := (List.pairwise_cons.mp hp).1 y (by simp)
      exact (hNo x (hL x (by simp)) y (hL y (by simp)) hxy).elim

theorem cliqueBound_orbits {R : V → V → Prop} [DecidableRel R]
    (S A : Finset V) (b : ℕ) (hCover : HasOrbitMaps R S A)
    (hChildren : ∀ a∈A,ListCliqueBound R (S.filter (R a)) b) :
    ListCliqueBound R S (b+1) := by
  intro L hL hp
  cases L with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y ys =>
      have hxS : x∈S := hL x (by simp)
      have htailMem : ∀ z∈(y::ys),z∈S := by
        intro z hz
        exact hL z (List.mem_cons_of_mem x hz)
      obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hp
      obtain ⟨a,ha,f,hfx,hfS,hfR⟩ :=
        hCover x hxS ⟨y,htailMem y (by simp),hhead y (by simp)⟩
      have hmemMapped : ∀ z∈(y::ys).map f,z∈S.filter (R a) := by
        intro z hz
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
        apply Finset.mem_filter.mpr
        refine ⟨hfS w (htailMem w hw),?_⟩
        have h := hfR x hxS w (htailMem w hw) (hhead w hw)
        simpa only [hfx] using h
      have hpmap := pairwise_map_on S f (y::ys) htailMem hfR htail
      have hbound := hChildren a ha ((y::ys).map f) hmemMapped hpmap
      simp only [List.length_map] at hbound
      exact Nat.succ_le_succ hbound

end EntropyDesigns.QuadraticRefinement
