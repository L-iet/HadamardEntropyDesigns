/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentratedFamily.GlobalCap
public import EntropySupportFace.FieldMasks
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.ConcentratedFamily
noncomputable section
open SupportFace
open scoped BigOperators

def binaryBit (z : ZMod 2) : Bool := decide (z=1)

theorem binaryBit_injective : Function.Injective binaryBit := by
  intro a b hab
  rcases binaryField_cases a with ha|ha <;>
    rcases binaryField_cases b with hb|hb <;> simp_all [binaryBit]

theorem binaryBit_sign (z : ZMod 2) : (bitSign (binaryBit z):ℝ)=binarySign z := by
  rcases binaryField_cases z with hz|hz <;> norm_num [binaryBit,binarySign,bitSign,hz]

theorem source_global_optimizer {k s : ℕ} (r : ℕ) (hkpow : k=2^r) (i0 : Fin k) :
    ∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧
      collision q=1/((k*2^s:ℕ):ℝ) ∧
      (∀ p : SourceOutcome k s i0 → ℝ,sourceFeasible i0 p → collision p≤collision q) := by
  classical
  let m := r+s
  have hC : Fintype.card (SourceCoordinate k s i0)=Fintype.card (NonzeroMask m) := by
    simp only [card_source_coordinates,card_nonzero_masks,m,hkpow,pow_add]
  let E : SourceCoordinate k s i0 ≃ NonzeroMask m := Fintype.equivOfCardEq hC
  let V := Fin m → ZMod 2
  let L : SourceCoordinate k s i0 → V →ₗ[ZMod 2] ZMod 2 := fun c => maskFunctional (E c).val
  have hLzero : ∀ c,L c≠0 := by
    intro c
    exact maskFunctional_nonzero (E c).val (Finset.nonempty_iff_ne_empty.mpr (E c).property)
  have hLinj : Function.Injective L := by
    intro c d h
    apply E.injective
    apply Subtype.ext
    exact maskFunctional_injective m h
  let f : V → SourceOutcome k s i0 := fun v c => binaryBit (L c v)
  let w : V → ℝ := fun _ => 1/(Fintype.card V:ℝ)
  let q := pushLaw f w
  have hf : Function.Injective f := by
    intro v w hfw
    funext a
    let c : SourceCoordinate k s i0 := E.symm ⟨{a},Finset.singleton_ne_empty a⟩
    have he : E c=⟨{a},Finset.singleton_ne_empty a⟩ := E.apply_symm_apply _
    have hv : L c v=L c w := binaryBit_injective (congrFun hfw c)
    change maskFunctional (E c).val v=maskFunctional (E c).val w at hv
    rw [he] at hv
    simpa [maskFunctional] using hv
  have hm := uniform_binary_character_moments L hLzero hLinj
  have hsign (v : V) (c : SourceCoordinate k s i0) : (bitSign (f v c):ℝ)=binarySign (L c v) :=
    binaryBit_sign _
  have hfeasible : sourceFeasible i0 q := by
    refine ⟨pushLaw_nonneg f w hm.1,(pushLaw_mass f w).trans hm.2.1,?_,?_⟩
    · intro c
      have hp := pushLaw_moment (α:=V) (β:=SourceOutcome k s i0) f w (fun y => (bitSign (y c):ℝ))
      change (∑ y,pushLaw f w y*(bitSign (y c):ℝ))=0
      rw [hp]
      simpa only [hsign,w] using hm.2.2.1 c
    · intro c d hcd
      have hp := pushLaw_moment (α:=V) (β:=SourceOutcome k s i0) f w
        (fun y => (bitSign (y c):ℝ)*(bitSign (y d):ℝ))
      change (∑ y,pushLaw f w y*(bitSign (y c):ℝ)*(bitSign (y d):ℝ))=0
      simp only [mul_assoc]
      rw [hp]
      simpa only [hsign,w,mul_assoc] using hm.2.2.2 c d hcd
  have hVcard : Fintype.card V=k*2^s := by
    simp only [V,Fintype.card_fun,Fintype.card_fin,ZMod.card,m,pow_add,hkpow]
  have hn : (Fintype.card V:ℝ)≠0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card V≠0)
  have hcollision : collision q=1/((k*2^s:ℕ):ℝ) := by
    calc
      collision q=collision w := pushLaw_injective_collision f hf w
      _=1/(Fintype.card V:ℝ) := by
        simp only [collision,w,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        field_simp
      _=_ := by rw [hVcard]
  refine ⟨q,hfeasible,hcollision,?_⟩
  intro p hp
  rw [hcollision]
  exact source_global_collision_cap i0 p hp

end
end EntropyDesigns.ConcentratedFamily
