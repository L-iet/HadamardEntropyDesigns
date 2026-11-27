/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Binary dual generators give exact coordinate-parity membership tests. -/
module
public import EntropyQuadraticClassification.QuadraticCheckTypes
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem binary_dot_zero_iff (f g : ι → ZMod 2) :
    (∑ z,f z*g z)=0 ↔ dotParity (oneSupport f) (oneSupport g)=0 := by
  rw [oneSupport_dot]
  exact ZMod.natCast_eq_natCast_iff' _ 0 2

theorem binary_span_orthogonal_iff (A : Set (ι → ZMod 2)) (x : ι → ZMod 2) :
    x∈(binaryFunctionDotForm ι).orthogonal (Submodule.span (ZMod 2) A) ↔
      ∀ h∈A,(binaryFunctionDotForm ι) h x=0 := by
  constructor
  · intro hx h hh
    exact hx h (Submodule.subset_span hh)
  · intro hx
    have hk : Submodule.span (ZMod 2) A ≤
        LinearMap.ker ((binaryFunctionDotForm ι).flip x) := by
      apply Submodule.span_le.mpr
      intro h hh
      exact hx h hh
    intro h hh
    exact hk hh

theorem binary_double_orthogonal (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    (binaryFunctionDotForm ι).orthogonal ((binaryFunctionDotForm ι).orthogonal C)=C := by
  have hrefl : (binaryFunctionDotForm ι).IsRefl := by
    intro f g h
    change (∑ z,g z*f z)=0
    change (∑ z,f z*g z)=0 at h
    simpa only [mul_comm] using h
  exact (binaryFunctionDotForm ι).orthogonal_orthogonal
    (binaryFunctionDotForm_nondegenerate ι) hrefl C

theorem binary_single_check_kernel (C : Submodule (ZMod 2) (ι → ZMod 2))
    (h : ι → ZMod 2)
    (hD : (binaryFunctionDotForm ι).orthogonal C=Submodule.span (ZMod 2) {h})
    (x : ι → ZMod 2) :
    x∈C ↔ dotParity (oneSupport h) (oneSupport x)=0 := by
  rw [←binary_double_orthogonal C,hD,binary_span_orthogonal_iff]
  have he : (∀ y∈({h} : Set (ι → ZMod 2)),(binaryFunctionDotForm ι) y x=0) ↔
      (binaryFunctionDotForm ι) h x=0 := by simp
  rw [he]
  exact binary_dot_zero_iff h x

theorem binary_two_check_kernel (C : Submodule (ZMod 2) (ι → ZMod 2))
    (h g : ι → ZMod 2)
    (hD : (binaryFunctionDotForm ι).orthogonal C=Submodule.span (ZMod 2) {h,g})
    (x : ι → ZMod 2) :
    x∈C ↔ dotParity (oneSupport h) (oneSupport x)=0 ∧
      dotParity (oneSupport g) (oneSupport x)=0 := by
  rw [←binary_double_orthogonal C,hD,binary_span_orthogonal_iff]
  have he : (∀ y∈({h,g} : Set (ι → ZMod 2)),(binaryFunctionDotForm ι) y x=0) ↔
      (binaryFunctionDotForm ι) h x=0 ∧ (binaryFunctionDotForm ι) g x=0 := by simp
  rw [he]
  exact and_congr (binary_dot_zero_iff h x) (binary_dot_zero_iff g x)

end EntropyDesigns.QuadraticRefinement
