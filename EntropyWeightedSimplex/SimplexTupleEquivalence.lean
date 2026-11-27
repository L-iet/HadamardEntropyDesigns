/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyWeightedSimplex.SimplexChoices
@[expose] public section
namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Classical

 theorem bounded_exponent_tuple_is_choice (cs : List ℝ) (hc : ∀ c∈cs,0<c)
    (L : ℝ) (a : Fin cs.length → ℕ) (ha : weightedExponentSum cs a≤L) :
    ∃ q : SimplexChoices cs L,choiceTuple cs L q=a := by
  induction cs generalizing L with
  | nil =>
    have hL : 0≤L := by simpa [weightedExponentSum] using ha
    exact ⟨⟨Unit.unit,hL⟩,funext (fun i => Fin.elim0 i)⟩
  | cons c cs ih =>
    have hcpos : 0<c := hc c (by simp)
    have hcs : ∀ x∈cs,0<x := fun x hx => hc x (by simp [hx])
    have hnonneg := weighted_exponent_sum_nonnegative cs hcs (Fin.tail a)
    have hroot := ha
    rw [weighted_exponent_sum_cons] at hroot
    have hL : 0≤L := (weighted_exponent_sum_nonnegative (c::cs) hc a).trans ha
    have hhead : (a 0:ℝ)≤L/c := by
      apply (le_div_iff₀ hcpos).mpr
      nlinarith
    have hnat : a 0≤⌊L/c⌋₊ := (Nat.le_floor_iff (div_nonneg hL hcpos.le)).mpr hhead
    have htail : weightedExponentSum cs (Fin.tail a)≤L-c*(a 0:ℝ) := by linarith
    obtain ⟨q,hq⟩ := ih hcs (L-c*(a 0:ℝ)) (Fin.tail a) htail
    refine ⟨⟨⟨a 0,by omega⟩,q⟩,?_⟩
    change Fin.cons (a 0) (choiceTuple cs (L-c*(a 0:ℝ)) q)=a
    rw [hq]
    exact Fin.cons_self_tail a

noncomputable def simplexChoiceEquivTuples (cs : List ℝ) (hc : ∀ c∈cs,0<c) (L : ℝ) :
    SimplexChoices cs L ≃ {a : Fin cs.length → ℕ // weightedExponentSum cs a≤L} :=
  Equiv.ofBijective (fun q => ⟨choiceTuple cs L q,choice_tuple_weight_bound cs L q⟩)
    ⟨fun x y he => choice_tuple_injective cs L (congrArg Subtype.val he),
      fun a => by
        obtain ⟨q,hq⟩ := bounded_exponent_tuple_is_choice cs hc L a.val a.property
        exact ⟨q,Subtype.ext hq⟩⟩

 theorem simplex_lattice_card (cs : List ℝ) (hc : ∀ c∈cs,0<c) (L : ℝ) :
    Nat.card {a : Fin cs.length → ℕ // weightedExponentSum cs a≤L}=simplexCount cs L := by
  calc
    _=Nat.card (SimplexChoices cs L) := (Nat.card_congr (simplexChoiceEquivTuples cs hc L)).symm
    _=Fintype.card (SimplexChoices cs L) := Nat.card_eq_fintype_card
    _=_ := simplex_choices_card cs L

 theorem weighted_simplex_lattice_bounds (cs : List ℝ) (hc : ∀ c∈cs,0<c)
    (L : ℝ) (hL : 0≤L) :
    L^cs.length/((cs.length.factorial:ℝ)*cs.prod)≤
        (Nat.card {a : Fin cs.length → ℕ // weightedExponentSum cs a≤L}:ℝ) ∧
    (Nat.card {a : Fin cs.length → ℕ // weightedExponentSum cs a≤L}:ℝ)≤
        (L+cs.sum)^cs.length/((cs.length.factorial:ℝ)*cs.prod) := by
  rw [simplex_lattice_card cs hc L]
  exact recursive_simplex_count_bounds cs hc L hL

end EntropyDesigns.WeightedSimplex
