/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyAffine.Rank
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dual.Lemmas
@[expose] public section
namespace EntropyDesigns
noncomputable section

theorem booleanAffineEvaluation_range (r : ℕ) :
    LinearMap.range (booleanAffineEvaluation r) = lowDegreeBooleanCode r 1 := by
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq (lowDegreeBooleanCode_one_affine r)
  have hdim : Module.finrank (ZMod 2)
      ((Fin r → ZMod 2) →ᵃ[ZMod 2] ZMod 2) = r+1 := by
    simp [AffineMap.finrank_eq]
  have hu := (booleanAffineEvaluation r).finrank_range_le
  have hl := Submodule.finrank_mono (lowDegreeBooleanCode_one_affine r)
  rw [degree_one_boolean_code_dimension] at hl
  rw [hdim] at hu
  rw [degree_one_boolean_code_dimension]
  omega

theorem booleanSupportVector_surjective (r : ℕ) :
    Function.Surjective (@booleanSupportVector r) := by
  intro v
  refine ⟨Finset.univ.filter (fun i => v i=1), ?_⟩
  funext i
  have hv : v i=0 ∨ v i=1 := by
    have h := ZMod.val_lt (v i)
    have he : (v i).val=0 ∨ (v i).val=1 := by omega
    rcases he with he|he
    · left; exact (ZMod.val_eq_zero (v i)).mp he
    · right; exact (ZMod.natCast_zmod_val (v i)).symm.trans (by rw [he]; rfl)
  rcases hv with h|h <;> simp [booleanSupportVector,h]

theorem booleanAffineEvaluation_injective (r : ℕ) :
    Function.Injective (booleanAffineEvaluation r) := by
  intro F G h
  ext v
  obtain ⟨z,rfl⟩ := booleanSupportVector_surjective r v
  exact congrFun h z


theorem proper_affine_subspace_separation {r : ℕ}
    (A : AffineSubspace (ZMod 2) (Fin r → ZMod 2))
    (hA : A≠⊤) (hne : (A : Set (Fin r → ZMod 2)).Nonempty) :
    ∃ F : (Fin r → ZMod 2) →ᵃ[ZMod 2] ZMod 2,
      F≠0 ∧ ∀ x∈A,F x=0 := by
  obtain ⟨p,hp⟩ := hne
  have hd : A.direction < ⊤ := lt_top_iff_ne_top.mpr
    (fun h => hA ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨p,hp⟩).mp h))
  obtain ⟨f,hf,hmap⟩ := A.direction.exists_dual_map_eq_bot_of_lt_top hd inferInstance
  let F : (Fin r → ZMod 2) →ᵃ[ZMod 2] ZMod 2 :=
    f.toAffineMap - AffineMap.const (ZMod 2) (Fin r → ZMod 2) (f p)
  refine ⟨F,?_,?_⟩
  · intro hz
    apply hf
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun G : (Fin r → ZMod 2) →ᵃ[ZMod 2] ZMod 2 => G (x+p)) hz
    simpa [F,map_add] using hx
  · intro x hx
    have hv := A.vsub_mem_direction hx hp
    have hm : f (x-p)∈A.direction.map f := Submodule.mem_map.mpr ⟨x-p,hv,rfl⟩
    rw [hmap] at hm
    simpa [F,map_sub] using hm

theorem fixedSupport_degree_sub_two_extension_iff {r : ℕ} (hr : 2≤r)
    (S : Finset (Finset (Fin r))) (hproper : S≠Finset.univ) :
    (∀ f : S → ZMod 2, ∃ g∈lowDegreeBooleanCode r (r-2), binaryFunctionRestriction S g=f) ↔
    affineSpan (ZMod 2) (Set.range (fun z : {z : Finset (Fin r) // z∉S} =>
      booleanSupportVector z.val))=⊤ := by
  constructor
  · intro hext
    by_contra hspan
    let A := affineSpan (ZMod 2) (Set.range (fun z : {z : Finset (Fin r) // z∉S} =>
      booleanSupportVector z.val))
    have hex : ∃ z,z∉S := by
      by_contra! h
      exact hproper (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨z,hz⟩ := hex
    have hmem : ∀ w,w∉S → booleanSupportVector w∈A := by
      intro w hw
      exact subset_affineSpan (ZMod 2) _ ⟨⟨w,hw⟩,rfl⟩
    obtain ⟨F,hF,hzero⟩ := proper_affine_subspace_separation A hspan ⟨_,hmem z hz⟩
    have hg : booleanAffineEvaluation r F∈lowDegreeBooleanCode r 1 := by
      rw [← booleanAffineEvaluation_range]
      exact LinearMap.mem_range.mpr ⟨F,rfl⟩
    have hcrit := (lowDegreeBooleanCode_extension_criterion (r:=r) (d:=r-2) (by omega) S).mp hext
    have hd : r-(r-2)-1=1 := by omega
    rw [hd] at hcrit
    have hzeroEval := hcrit _ hg (fun w hw => hzero _ (hmem w hw))
    apply hF
    apply booleanAffineEvaluation_injective r
    simpa using hzeroEval
  · exact affineSpanningComplement_degree_sub_two_extension hr S

end
end EntropyDesigns
