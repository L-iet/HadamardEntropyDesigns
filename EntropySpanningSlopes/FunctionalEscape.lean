/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Algebra.Basic
@[expose] public section
namespace EntropyDesigns.SpanningSlopes
noncomputable section
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

def rightMulLinear (b : K) : K →ₗ[F] K where
  toFun t := t*b
  map_add' x y := by simp only [add_mul]
  map_smul' c t := by exact smul_mul_assoc c t b

theorem spanning_set_escapes_scaled_kernel (R : Set K)
    (hspan : Submodule.span F R=⊤) (f : K →ₗ[F] F) (hf : f≠0)
    (b : K) (hb : b≠0) : ∃ t∈R,f (t*b)≠0 := by
  classical
  by_contra hex
  let g : K →ₗ[F] F := f.comp (rightMulLinear b)
  have hsubset : R⊆LinearMap.ker g := by
    intro t ht
    change f (t*b)=0
    by_contra hn
    exact hex ⟨t,ht,hn⟩
  have htop : (⊤ : Submodule F K)≤LinearMap.ker g := by
    simpa only [hspan] using (Submodule.span_le.mpr hsubset)
  have hg (z : K) : g z=0 := htop (show z∈(⊤ : Submodule F K) from trivial)
  apply hf
  apply LinearMap.ext
  intro z
  have hz := hg (z*b⁻¹)
  simpa [g,rightMulLinear,mul_assoc,hb] using hz

end
end EntropyDesigns.SpanningSlopes
