/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.FieldCoordinates
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis
@[expose] public section
namespace EntropyDesigns.SpanningSlopes
noncomputable section
open SupportFace

theorem exists_nonzero_spanning_finset {s u : ℕ} (hs : s≠0)
    (hsu : s≤u) (hu : u<2^s) :
    ∃ R : Finset (GaloisField 2 s),R.card=u ∧ 0∉R ∧
      Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤ := by
  classical
  let K := GaloisField 2 s
  letI : Fintype K := Fintype.ofFinite K
  let B : Module.Basis (Fin s) (ZMod 2) K :=
    (Pi.basisFun (ZMod 2) (Fin s)).map (fieldCoordinates s hs).symm
  let S : Finset K := Finset.univ.image B
  let U : Finset K := Finset.univ.erase 0
  have hScard : S.card=s := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ B.injective]
    simp
  have hSU : S⊆U := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨B.ne_zero i,Finset.mem_univ _⟩
  have hSset : (S:Set K)=Set.range B := by
    ext x
    simp [S]
  have hSspan : Submodule.span (ZMod 2) (S:Set K)=⊤ := by
    rw [hSset]
    exact B.span_eq
  have hKcard : Fintype.card K=2^s := by
    simpa only [Nat.card_eq_fintype_card] using GaloisField.card (p:=2) (n:=s) hs
  have hUcard : U.card=2^s-1 := by simp [U,hKcard]
  have hSu : S.card≤u := by rw [hScard];exact hsu
  have huU : u≤U.card := by rw [hUcard];omega
  obtain ⟨R,hSR,hRU,hRcard⟩ := Finset.exists_subsuperset_card_eq hSU hSu huU
  refine ⟨R,hRcard,?_,?_⟩
  · intro hzero
    exact (Finset.mem_erase.mp (hRU hzero)).1 rfl
  · apply top_unique
    rw [←hSspan]
    exact Submodule.span_mono hSR

theorem enumerate_finset_with_anchor {K : Type*} [DecidableEq K]
    (P : Finset K) {k : ℕ} (hcard : P.card=k) (a0 : K) (ha0 : a0∈P) (i0 : Fin k) :
    ∃ t : Fin k → K,Function.Injective t ∧ t i0=a0 ∧
      (∀ x : K,(∃ i,t i=x) ↔ x∈P) := by
  classical
  let b : Fin k ≃ {x // x∈P} := Fintype.equivOfCardEq (by simp [hcard])
  let j0 := b.symm ⟨a0,ha0⟩
  let σ := Equiv.swap i0 j0
  let t : Fin k → K := fun i => (b (σ i)).val
  refine ⟨t,Subtype.val_injective.comp (b.injective.comp σ.injective),?_,?_⟩
  · change (b (Equiv.swap i0 j0 i0)).val=a0
    rw [Equiv.swap_apply_left]
    exact congrArg Subtype.val (b.apply_symm_apply ⟨a0,ha0⟩)
  · intro x
    constructor
    · rintro ⟨i,rfl⟩
      exact (b (σ i)).property
    · intro hx
      refine ⟨σ.symm (b.symm ⟨x,hx⟩),?_⟩
      change (b (σ (σ.symm (b.symm ⟨x,hx⟩)))).val=x
      rw [σ.apply_symm_apply,b.apply_symm_apply]

end
end EntropyDesigns.SpanningSlopes
