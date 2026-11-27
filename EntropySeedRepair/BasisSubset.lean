/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupport.AffineSeparation
public import Mathlib.LinearAlgebra.AffineSpace.Basis
@[expose] public section
namespace EntropyDesigns.SupportRepair
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem independent_span_intersection {r : ℕ}
    (A B : Set (Fin r → ZMod 2)) (hBA : B⊆A)
    (hA : AffineIndependent (ZMod 2) (fun x : A => x.val))
    (x : Fin r → ZMod 2) (hxA : x∈A) (hxspan : x∈affineSpan (ZMod 2) B) : x∈B := by
  let J : Set A := {a | a.val∈B}
  have him : ((fun a : A => a.val) '' J)=B := by
    ext y
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro hy
      exact ⟨⟨y,hBA hy⟩,hy,rfl⟩
  have hiff := hA.mem_affineSpan_iff (⟨x,hxA⟩ : A) J
  rw [him] at hiff
  exact hiff.mp hxspan

theorem finite_affine_basis_subset {r : ℕ} (T : Finset (Fin r → ZMod 2))
    (hT : T.Nonempty) :
    ∃ B : Finset (Fin r → ZMod 2),B⊆T ∧
      AffineIndependent (ZMod 2) (fun x : (B : Set (Fin r → ZMod 2)) => x.val) ∧
      affineSpan (ZMod 2) (B : Set (Fin r → ZMod 2))=
        affineSpan (ZMod 2) (T : Set (Fin r → ZMod 2)) ∧
      B.card=Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (T : Set (Fin r → ZMod 2)))+1 := by
  classical
  obtain ⟨B,hBT,hspan,hB⟩ := exists_affineIndependent (ZMod 2) (Fin r → ZMod 2)
    (T : Set (Fin r → ZMod 2))
  let F : Finset (Fin r → ZMod 2) := B.toFinite.toFinset
  have hcoe : (F : Set (Fin r → ZMod 2))=B := B.toFinite.coe_toFinset
  have hnonbot : affineSpan (ZMod 2) (T : Set (Fin r → ZMod 2))≠⊥ := by
    intro he
    obtain ⟨x,hx⟩ := hT
    have hh := mem_affineSpan (ZMod 2) (show x∈(T : Set (Fin r → ZMod 2)) from hx)
    rw [he] at hh
    exact hh
  have hc := hB.ncard_eq_succ_finDim_affineSpan
  rw [hspan,AffineSubspace.finDim_eq_finrank hnonbot,direction_affineSpan,WithBot.succ_natCast] at hc
  refine ⟨F,?_,?_,?_,?_⟩
  · intro x hx
    exact hBT (B.toFinite.mem_toFinset.mp hx)
  · rw [hcoe]
    exact hB
  · simpa only [hcoe] using hspan
  · rw [Set.ncard_eq_toFinset_card B B.toFinite] at hc
    exact hc

theorem finite_full_affine_basis_extension {r : ℕ}
    (B : Finset (Fin r → ZMod 2))
    (hB : AffineIndependent (ZMod 2) (fun x : (B : Set (Fin r → ZMod 2)) => x.val)) :
    ∃ A : Finset (Fin r → ZMod 2),B⊆A ∧
      AffineIndependent (ZMod 2) (fun x : (A : Set (Fin r → ZMod 2)) => x.val) ∧
      affineSpan (ZMod 2) (A : Set (Fin r → ZMod 2))=⊤ ∧ A.card=r+1 := by
  classical
  obtain ⟨A,hBA,hA,hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hB
  let F : Finset (Fin r → ZMod 2) := A.toFinite.toFinset
  have hcoe : (F : Set (Fin r → ZMod 2))=A := A.toFinite.coe_toFinset
  have hc := hA.ncard_eq_succ_finDim_affineSpan
  rw [hspan,AffineSubspace.finDim_eq_finrank (by simp),AffineSubspace.direction_top] at hc
  have hc' : F.card=r+1 := by
    rw [Set.ncard_eq_toFinset_card A A.toFinite] at hc
    simpa [F,WithBot.succ_natCast] using hc
  refine ⟨F,?_,?_,?_,hc'⟩
  · intro x hx
    exact A.toFinite.mem_toFinset.mpr (hBA hx)
  · rw [hcoe]
    exact hA
  · simpa only [hcoe] using hspan

end
end EntropyDesigns.SupportRepair
