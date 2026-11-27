/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
@[expose] public section
namespace EntropyDesigns
noncomputable section

def squarefreeBooleanMonomial {ι : Type*} [DecidableEq ι]
    (s z : Finset ι) : ZMod 2 := if s ⊆ z then 1 else 0

def lowDegreeBooleanCode (r d : ℕ) : Submodule (ZMod 2) (Finset (Fin r) → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (fun s : {s : Finset (Fin r) // s.card≤d} =>
    squarefreeBooleanMonomial s.val))

def booleanValueSign (a : ZMod 2) : ℤ := if a=0 then 1 else -1

def HasAffineSeedExtension {N r : ℕ} (labels : Fin N → Finset (Fin r))
    (g : Finset (Fin r) → ZMod 2) : Prop :=
  ∃ h∈lowDegreeBooleanCode r 1,∀ j,h (labels j)=g (labels j)

open scoped Classical in
def affineSeedColumnSet {N m r : ℕ} (labels : Fin N → Finset (Fin r))
    (f : Fin m → (Finset (Fin r) → ZMod 2)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => HasAffineSeedExtension labels (f i))

theorem affine_hadamard_seed_observable_budget {d r : ℕ}
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H)
    (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1)
    (hres : (d+1)%8=4) (hr : r<(d+1)-2) (hgap : d+1<2^r)
    (labels : Fin (d+1) → Finset (Fin r)) (hinj : Function.Injective labels)
    (f : Fin d → (Finset (Fin r) → ZMod 2))
    (hmatch : ∀ j i,booleanValueSign (f i (labels j))=H j i.succ) :
    (affineSeedColumnSet labels f).card≤min r (2^r-(d+1)-1) := by sorry

theorem twelve_seed_nonaffine_budget
    (H : Matrix (Fin 12) (Fin 12) ℤ) (hH : Matrix.IsHadamard H) (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ 11⟩=1)
    (labels : Fin 12 → Finset (Fin 4)) (hinj : Function.Injective labels)
    (f : Fin 11 → (Finset (Fin 4) → ZMod 2))
    (hmatch : ∀ j i,booleanValueSign (f i (labels j))=H j i.succ) :
    (affineSeedColumnSet labels f).card≤3 ∧ 8≤11-(affineSeedColumnSet labels f).card := by sorry

theorem twenty_seed_nonaffine_budget
    (H : Matrix (Fin 20) (Fin 20) ℤ) (hH : Matrix.IsHadamard H) (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ 19⟩=1)
    (labels : Fin 20 → Finset (Fin 5)) (hinj : Function.Injective labels)
    (f : Fin 19 → (Finset (Fin 5) → ZMod 2))
    (hmatch : ∀ j i,booleanValueSign (f i (labels j))=H j i.succ) :
    (affineSeedColumnSet labels f).card≤5 ∧ 14≤19-(affineSeedColumnSet labels f).card := by sorry

def booleanSupportIndicator {r : ℕ} (S : Finset (Finset (Fin r))) (z : Finset (Fin r)) : ZMod 2 :=
  if z∈S then 1 else 0

theorem degree_one_boolean_code_dimension (r : ℕ) :
    Module.finrank (ZMod 2) (lowDegreeBooleanCode r 1)=r+1 := by sorry

theorem residue_four_support_indicator_not_affine {r : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hres : S.card%8=4) :
    booleanSupportIndicator S∉lowDegreeBooleanCode r 1 := by sorry

end
end EntropyDesigns
