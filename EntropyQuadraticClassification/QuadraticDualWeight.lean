/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
The actual quadratic restriction code has constant-weight-eight nonzero dual words. -/
module
public import EntropyQuadraticClassification.AffineBalance
public import EntropySupport.RestrictionDimension
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement

noncomputable def supportVectorEquiv (r : ℕ) :
    Finset (Fin r) ≃ (Fin r → ZMod 2) := by
  classical
  refine Equiv.ofBijective booleanSupportVector ⟨?_,booleanSupportVector_surjective r⟩
  intro A B h
  ext i
  have hi := congrFun h i
  by_cases ha : i∈A <;> by_cases hb : i∈B <;>
    simp [booleanSupportVector,ha,hb] at hi ⊢

theorem one_count_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : A → ZMod 2) (g : B → ZMod 2) (h : ∀ a,f a=g (e a)) :
    (Finset.univ.filter (fun a => f a=1)).card=
      (Finset.univ.filter (fun b => g b=1)).card := by
  classical
  apply Finset.card_equiv e
  intro a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,h]

theorem zero_extend_one_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (g : S → ZMod 2) :
    (Finset.univ.filter (fun z => binaryFunctionZeroExtend S g z=1)).card=
      (Finset.univ.filter (fun z : S => g z=1)).card := by
  classical
  let e : {z : ι // binaryFunctionZeroExtend S g z=1} ≃ {z : S // g z=1} :=
    { toFun := fun z => by
        have hz : z.val∈S := by
          by_contra hz
          have h := z.property
          simp [binaryFunctionZeroExtend,hz] at h
        exact ⟨⟨z.val,hz⟩,by simpa [binaryFunctionZeroExtend,hz] using z.property⟩
      invFun := fun z => ⟨z.val.val,by
        simpa only [binaryFunctionZeroExtend_on] using z.property⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun z => Subtype.ext (Subtype.ext rfl) }
  calc
    _ = Fintype.card {z : ι // binaryFunctionZeroExtend S g z=1} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card {z : S // g z=1} := Fintype.card_congr e
    _ = _ := Fintype.card_subtype _

theorem quadratic_dual_weight_eight
    (S : Finset (Finset (Fin 4))) (hproper : S≠Finset.univ)
    (g : S → ZMod 2)
    (hg : g∈(binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S)))
    (hne : g≠0) :
    (Finset.univ.filter (fun z : S => g z=1)).card=8 := by
  classical
  let extg := binaryFunctionZeroExtend S g
  have hext := (binaryFunctionRestriction_orthogonal S (lowDegreeBooleanCode 4 2) g).mp hg
  change extg∈(booleanCubeDotForm 4).orthogonal (lowDegreeBooleanCode 4 2) at hext
  rw [lowDegreeBooleanCode_duality (by decide : 2<4)] at hext
  let gcode : lowDegreeBooleanCode 4 1 := ⟨extg,hext⟩
  let F := (booleanAffineEvaluationCodeEquiv 4).symm gcode
  have hEval : ∀ z,F (booleanSupportVector z)=extg z :=
    fun z => affineCodeEquiv_inverse_value gcode z
  have hex : ∃ z,z∉S := by
    by_contra h
    apply hproper
    apply Finset.eq_univ_iff_forall.mpr
    intro z
    by_contra hz
    exact h ⟨z,hz⟩
  obtain ⟨z0,hz0⟩ := hex
  have hp : F (booleanSupportVector z0)=0 := by
    rw [hEval]
    simp [extg,binaryFunctionZeroExtend,hz0]
  have hF : F≠0 := by
    intro hzero
    apply hne
    funext z
    have h := hEval z.val
    rw [hzero] at h
    change 0=binaryFunctionZeroExtend S g z.val at h
    rw [binaryFunctionZeroExtend_on] at h
    exact h.symm
  calc
    _ = (Finset.univ.filter (fun z => extg z=1)).card :=
      (zero_extend_one_count S g).symm
    _ = (Finset.univ.filter (fun v : Fin 4 → ZMod 2 => F v=1)).card :=
      one_count_equiv (supportVectorEquiv 4) extg F (fun z => (hEval z).symm)
    _ = 8 := affine_four_one_count F (booleanSupportVector z0) hp hF

end EntropyDesigns.QuadraticRefinement
