/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyWeightedSimplex.SimplexTupleEquivalence
@[expose] public section
namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Classical

 theorem finite_simplex_index_transport {r : ℕ} (c : Fin r → ℝ) (L : ℝ) :
    Nat.card {a : Fin (List.ofFn c).length → ℕ // weightedExponentSum (List.ofFn c) a≤L}=
      Nat.card {a : Fin r → ℕ // (∑ i,c i*(a i:ℝ))≤L} := by
  let cs := List.ofFn c
  have hlen : cs.length=r := List.length_ofFn
  let e : Fin cs.length ≃ Fin r :=
    { toFun := Fin.cast hlen
      invFun := Fin.cast hlen.symm
      left_inv := fun i => by apply Fin.ext;rfl
      right_inv := fun i => by apply Fin.ext;rfl }
  let E : (Fin cs.length → ℕ) ≃ (Fin r → ℕ) :=
    { toFun := fun a j => a (e.symm j)
      invFun := fun a i => a (e i)
      left_inv := fun a => by funext i;simp
      right_inv := fun a => by funext i;simp }
  have hcoeff (i : Fin cs.length) : cs.get i=c (e i) := by
    change (List.ofFn c).get i=c (Fin.cast hlen i)
    rw [List.get_ofFn]
  have hsum (a : Fin cs.length → ℕ) : weightedExponentSum cs a=∑ j,c j*(E a j:ℝ) := by
    calc
      _=∑ i,c (e i)*(a i:ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hcoeff]
      _=_ := by
        simpa only [E,Equiv.coe_fn_mk,Equiv.symm_apply_apply] using
          Equiv.sum_comp e (fun j => c j*(a (e.symm j):ℝ))
  apply Nat.card_congr
  exact E.subtypeEquiv (p := fun a => weightedExponentSum cs a≤L)
    (q := fun a => (∑ i,c i*(a i:ℝ))≤L) (fun a => by rw [hsum])

 theorem finite_weighted_simplex_bounds {r : ℕ} (c : Fin r → ℝ) (hc : ∀ i,0<c i)
    (L : ℝ) (hL : 0≤L) :
    L^r/((r.factorial:ℝ)*(∏ i,c i))≤
        (Nat.card {a : Fin r → ℕ // (∑ i,c i*(a i:ℝ))≤L}:ℝ) ∧
    (Nat.card {a : Fin r → ℕ // (∑ i,c i*(a i:ℝ))≤L}:ℝ)≤
        (L+∑ i,c i)^r/((r.factorial:ℝ)*(∏ i,c i)) := by
  have hcs : ∀ x∈List.ofFn c,0<x := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hc i
  have hh := weighted_simplex_lattice_bounds (List.ofFn c) hcs L hL
  rw [finite_simplex_index_transport c L] at hh
  simpa only [List.length_ofFn,List.prod_ofFn,List.sum_ofFn] using hh

end EntropyDesigns.WeightedSimplex
