/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.BinaryHyperplanes
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
@[expose] public section
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

def binarySign (z : ZMod 2) : ℝ := if z=0 then 1 else -1

theorem binarySign_add (z w : ZMod 2) : binarySign (z+w)=binarySign z*binarySign w := by
  have h11 : (1:ZMod 2)+1=0 := by decide
  rcases binaryField_cases z with hz|hz <;> rcases binaryField_cases w with hw|hw <;>
    norm_num [binarySign,hz,hw,h11]

theorem binarySign_sub (z w : ZMod 2) : binarySign (z-w)=binarySign z*binarySign w := by
  have hn : -(1:ZMod 2)=1 := by decide
  rcases binaryField_cases z with hz|hz <;> rcases binaryField_cases w with hw|hw <;>
    norm_num [binarySign,hz,hw,hn]

theorem binarySign_mul_self (z : ZMod 2) : binarySign z*binarySign z=1 := by
  by_cases h : z=0 <;> simp [binarySign,h]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

theorem nonzero_binary_functional_hits_one (f : V →ₗ[ZMod 2] ZMod 2) (hf : f≠0) :
    ∃ v,f v=1 := by
  by_contra h
  apply hf
  ext v
  rcases binaryField_cases (f v) with h0|h1
  · exact h0
  · exact False.elim (h ⟨v,h1⟩)

theorem binary_functional_sum_zero (f : V →ₗ[ZMod 2] ZMod 2) (hf : f≠0) :
    (∑ x : V,binarySign (f x))=0 := by
  obtain ⟨v,hv⟩ := nonzero_binary_functional_hits_one f hf
  have hflip (x : V) : binarySign (f (v+x))= -binarySign (f x) := by
    rw [map_add,binarySign_add,hv]
    have h1 : binarySign (1:ZMod 2)=(-1:ℝ) := by norm_num [binarySign]
    rw [h1]
    ring
  have hsum := Equiv.sum_comp (Equiv.addLeft v) (fun x : V => binarySign (f x))
  change (∑ x : V,binarySign (f (v+x)))=(∑ x : V,binarySign (f x)) at hsum
  simp_rw [hflip,Finset.sum_neg_distrib] at hsum
  linarith

theorem distinct_binary_functionals_orthogonal (f g : V →ₗ[ZMod 2] ZMod 2) (hfg : f≠g) :
    (∑ x : V,binarySign (f x)*binarySign (g x))=0 := by
  have h := binary_functional_sum_zero (f-g) (sub_ne_zero.mpr hfg)
  simpa only [LinearMap.sub_apply,binarySign_sub] using h

theorem binary_functionals_orthogonality [DecidableEq (V →ₗ[ZMod 2] ZMod 2)] (f g : V →ₗ[ZMod 2] ZMod 2) :
    (∑ x : V,binarySign (f x)*binarySign (g x))=if f=g then (Fintype.card V:ℝ) else 0 := by
  by_cases h : f=g
  · subst g;simp [binarySign_mul_self]
  · simpa [h] using distinct_binary_functionals_orthogonal f g h

theorem uniform_binary_character_moments {I : Type*} (L : I → V →ₗ[ZMod 2] ZMod 2)
    (hzero : ∀ i,L i≠0) (hinj : Function.Injective L) :
    (∀ x : V,0≤1/(Fintype.card V:ℝ)) ∧
    ((∑ x : V,1/(Fintype.card V:ℝ))=1) ∧
    (∀ i,(∑ x : V,(1/(Fintype.card V:ℝ))*binarySign (L i x))=0) ∧
    (∀ i j,i≠j → (∑ x : V,(1/(Fintype.card V:ℝ))*binarySign (L i x)*binarySign (L j x))=0) := by
  have hcard : (0:ℝ)<Fintype.card V := by exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0:V)⟩)
  refine ⟨fun _ => (one_div_pos.mpr hcard).le,?_,?_,?_⟩
  · simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp [ne_of_gt hcard]
  · intro i
    rw [← Finset.mul_sum,binary_functional_sum_zero (L i) (hzero i),mul_zero]
  · intro i j hij
    have hL : L i≠L j := fun h => hij (hinj h)
    simp only [mul_assoc,← Finset.mul_sum,distinct_binary_functionals_orthogonal (L i) (L j) hL,mul_zero]
end
end EntropyDesigns.SupportFace
