/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Certificates
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped symmDiff

def HasAffineSeedExtension {N r : ℕ} (labels : Fin N → Finset (Fin r))
    (g : Finset (Fin r) → ZMod 2) : Prop :=
  ∃ h∈lowDegreeBooleanCode r 1,∀ j,h (labels j)=g (labels j)

theorem affine_seed_extension_of_mem {N r : ℕ} (labels : Fin N → Finset (Fin r))
    (g : Finset (Fin r) → ZMod 2) (hg : g∈lowDegreeBooleanCode r 1) :
    HasAffineSeedExtension labels g := ⟨g,hg,fun _ => rfl⟩

theorem boolean_restriction_parallelogram_not_affine {N r : ℕ}
    (labels : Fin N → Finset (Fin r)) (g : Finset (Fin r) → ZMod 2)
    (a b c z : Fin N) (hab : labels c=labels a∆labels b) (hzero : labels z=∅)
    (hfail : g (labels c)+g (labels z)≠g (labels a)+g (labels b)) :
    ¬HasAffineSeedExtension labels g := by
  rintro ⟨h,hh,hvalues⟩
  have hp := degree_one_boolean_parallelogram h hh (labels a) (labels b)
  rw [←hab,←hzero] at hp
  simp_rw [hvalues] at hp
  exact hfail hp

end
end EntropyDesigns
