/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupport.EvenRestrictionDimension
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

theorem evenCode_radical_dimension {ι : Type*} [Fintype ι]
    (C : Submodule (ZMod 2) (ι → ZMod 2))
    (hone : (fun _ : ι => (1 : ZMod 2))∈evenBinaryCode C)
    (hn : (fun _ : ι => (1 : ZMod 2))∉(binaryFunctionDotForm ι).orthogonal C)
    (hdual : (binaryFunctionDotForm ι).orthogonal C≤evenBinaryCode C) :
    (binaryFunctionDotForm ι).orthogonal (evenBinaryCode C)≤evenBinaryCode C ∧
    Module.finrank (ZMod 2) ↥(evenBinaryCode C ⊓
      (binaryFunctionDotForm ι).orthogonal (evenBinaryCode C))=
      Fintype.card ι-Module.finrank (ZMod 2) C+1 := by
  let B := binaryFunctionDotForm ι
  let E := evenBinaryCode C
  let one : ι → ZMod 2 := fun _ => 1
  let D := B.orthogonal C ⊔ Submodule.span (ZMod 2) {one}
  have hE : Module.finrank (ZMod 2) E=Module.finrank (ZMod 2) C-1 := evenBinaryCode_finrank C hn
  have hD : Module.finrank (ZMod 2) D=Fintype.card ι-Module.finrank (ZMod 2) C+1 := by
    rw [Submodule.finrank_sup_span_singleton hn]
    rw [B.finrank_orthogonal (binaryFunctionDotForm_nondegenerate ι)]
    simp
  have hDorth : D≤B.orthogonal E := by
    apply sup_le
    · intro g hg f hf
      exact hg f hf.1
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      intro f hf
      have hz : binaryParityLinear ι f=0 := hf.2
      simpa [B,one,binaryFunctionDotForm,dotProduct,binaryParityLinear] using hz
  have hDE : D≤E := sup_le hdual ((Submodule.span_singleton_le_iff_mem _ _).mpr hone)
  have hbC := Submodule.finrank_le C
  have hbD := Submodule.finrank_le D
  have hO := B.finrank_orthogonal (binaryFunctionDotForm_nondegenerate ι) E
  simp only [Module.finrank_fintype_fun_eq_card] at hbC hbD hO
  have hdEq : D=B.orthogonal E := by
    apply Submodule.eq_of_le_of_finrank_eq hDorth
    omega
  have hOE : B.orthogonal E≤E := hdEq ▸ hDE
  refine ⟨hOE,?_⟩
  have heq : E ⊓ B.orthogonal E=B.orthogonal E := inf_eq_right.mpr hOE
  rw [heq,← hdEq]
  exact hD

theorem lowDegreeBooleanCode_mono {r d e : ℕ} (hde : d≤e) :
    lowDegreeBooleanCode r d≤lowDegreeBooleanCode r e := by
  apply Submodule.span_mono
  rintro _ ⟨s,rfl⟩
  exact ⟨⟨s.val,s.property.trans hde⟩,rfl⟩

theorem degree_sub_two_restriction_dual_even {r : ℕ} (hr : 3≤r)
    (S : Finset (Finset (Fin r))) :
    (binaryFunctionDotForm S).orthogonal ((lowDegreeBooleanCode r (r-2)).map (binaryFunctionRestriction S))≤
      evenBinaryCode ((lowDegreeBooleanCode r (r-2)).map (binaryFunctionRestriction S)) := by
  intro g hg
  have hf := (binaryFunctionRestriction_orthogonal S (lowDegreeBooleanCode r (r-2)) g).mp hg
  change binaryFunctionZeroExtend S g∈(booleanCubeDotForm r).orthogonal (lowDegreeBooleanCode r (r-2)) at hf
  rw [lowDegreeBooleanCode_duality (by omega : r-2<r)] at hf
  have hd : r-(r-2)-1=1 := by omega
  rw [hd] at hf
  refine ⟨Submodule.mem_map.mpr ⟨binaryFunctionZeroExtend S g,
    lowDegreeBooleanCode_mono (by omega : 1≤r-2) hf,?_⟩,?_⟩
  · funext z
    exact binaryFunctionZeroExtend_on S g z
  · have hc : (fun _ : S => (1 : ZMod 2))∈
        (lowDegreeBooleanCode r (r-2)).map (binaryFunctionRestriction S) :=
      Submodule.mem_map.mpr ⟨fun _ => 1,lowDegreeBooleanCode_one_mem r (r-2),rfl⟩
    have hh := hg _ hc
    simpa [binaryFunctionDotForm,dotProduct,binaryParityLinear] using hh

theorem degree_sub_two_restriction_constant_even {r : ℕ}
    (S : Finset (Finset (Fin r))) (hres : S.card%8=4) :
    (fun _ : S => (1 : ZMod 2))∈
      evenBinaryCode ((lowDegreeBooleanCode r (r-2)).map (binaryFunctionRestriction S)) := by
  refine ⟨Submodule.mem_map.mpr ⟨fun _ => 1,lowDegreeBooleanCode_one_mem r (r-2),rfl⟩,?_⟩
  change (∑ _ : S,(1 : ZMod 2))=0
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one]
  exact (ZMod.natCast_eq_natCast_iff' S.card 0 2).mpr (by omega)

theorem degree_sub_two_restriction_radical_dimension {r : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hproper : S≠Finset.univ) (hres : S.card%8=4) :
    Module.finrank (ZMod 2) ↥(evenBinaryCode ((lowDegreeBooleanCode r (r-2)).map (binaryFunctionRestriction S)) ⊓
      (binaryFunctionDotForm S).orthogonal (evenBinaryCode ((lowDegreeBooleanCode r (r-2)).map (binaryFunctionRestriction S))))=
      r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))+1 := by
  have hh := (evenCode_radical_dimension _ (degree_sub_two_restriction_constant_even S hres)
    (restriction_code_one_not_orthogonal hr S hres) (degree_sub_two_restriction_dual_even (by omega) S)).2
  have hd := restrictionOrthogonal_finrank S (lowDegreeBooleanCode r (r-2))
  have hdim := degree_sub_two_restriction_dimension (by omega) S hproper
  rw [hdim] at hh
  simp only [Fintype.card_coe] at hh
  have he := (affineCodeSupported_equiv_vanishing S).finrank_eq
  have hne : (omittedBooleanVectors S).Nonempty := by
    have hex : ∃ z,z∉S := by
      by_contra! h
      exact hproper (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨z,hz⟩ := hex
    exact ⟨booleanSupportVector z,⟨z,by simpa using hz,rfl⟩⟩
  rw [affineVanishing_dimension _ hne] at he
  change _+Module.finrank (ZMod 2) ↥((booleanCubeDotForm r).orthogonal (lowDegreeBooleanCode r (r-2)) ⊓ supportedBinaryFunctions S)=_ at hd
  rw [lowDegreeBooleanCode_duality (by omega : r-2<r)] at hd
  have hdeg : r-(r-2)-1=1 := by omega
  rw [hdeg,he] at hd
  omega


def binaryCodeRadical {ι : Type*} [Fintype ι]
    (C : Submodule (ZMod 2) (ι → ZMod 2)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  C ⊓ (binaryFunctionDotForm ι).orthogonal C

def binaryBilinearRank {ι : Type*} [Fintype ι]
    (C : Submodule (ZMod 2) (ι → ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range
    (fun x : C => fun y : C => ∑ i,x.val i*y.val i)))

theorem binaryBilinearRank_eq {ι : Type*} [Fintype ι]
    (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    binaryBilinearRank C=Module.finrank (ZMod 2) C-Module.finrank (ZMod 2) (binaryCodeRadical C) := by
  let B := binaryFunctionDotForm ι
  let A : C →ₗ[ZMod 2] (C → ZMod 2) :=
    { toFun := fun x y => B x.val y.val
      map_add' := by intro x y; funext z; simp
      map_smul' := by intro c x; funext z; simp }
  have hspan : Submodule.span (ZMod 2) (Set.range
      (fun x : C => fun y : C => ∑ i,x.val i*y.val i))=LinearMap.range A := by
    change Submodule.span (ZMod 2) (LinearMap.range A : Set (C → ZMod 2))=LinearMap.range A
    exact Submodule.span_eq _
  have hsymm : ∀ x y,B x y=B y x := by
    intro x y
    simp [B,binaryFunctionDotForm,dotProduct,mul_comm]
  have he : (LinearMap.ker A).map C.subtype=binaryCodeRadical C := by
    ext v
    constructor
    · rintro ⟨g,hg,rfl⟩
      refine ⟨g.property,?_⟩
      intro x hx
      have hh := congrArg (fun L : C → ZMod 2 => L ⟨x,hx⟩) hg
      change B g.val x=0 at hh
      rwa [hsymm] at hh
    · rintro ⟨hv,ho⟩
      refine ⟨⟨v,hv⟩,?_,rfl⟩
      funext x
      change B v x.val=0
      rw [hsymm]
      exact ho x.val x.property
  have hm := Submodule.finrank_map_subtype_eq C (LinearMap.ker A)
  rw [he] at hm
  have hd := A.finrank_range_add_finrank_ker
  change binaryBilinearRank C= _
  unfold binaryBilinearRank
  rw [hspan]
  omega

theorem punctured_reed_muller_radical_dimensions {r : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hproper : S≠Finset.univ) (hres : S.card%8=4) :
    let a := r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))
    let C := (lowDegreeBooleanCode r (r-2)).map (binaryFunctionRestriction S)
    Module.finrank (ZMod 2) C=S.card-a ∧
    Module.finrank (ZMod 2) (evenBinaryCode C)=S.card-a-1 ∧
    Module.finrank (ZMod 2) (binaryCodeRadical (evenBinaryCode C))=a+1 ∧
    binaryBilinearRank (evenBinaryCode C)=S.card-2*a-2 := by
  dsimp only
  have hc := degree_sub_two_restriction_dimension (by omega) S hproper
  have he := degree_sub_two_even_restriction_dimension hr S hproper hres
  have hd := degree_sub_two_restriction_radical_dimension hr S hproper hres
  refine ⟨hc,he,hd,?_⟩
  rw [binaryBilinearRank_eq,he]
  change _-Module.finrank (ZMod 2) (binaryCodeRadical _)=_
  unfold binaryCodeRadical
  rw [hd]
  omega

end
end EntropyDesigns
