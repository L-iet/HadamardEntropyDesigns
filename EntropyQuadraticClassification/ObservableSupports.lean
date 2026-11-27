/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Balanced, orthogonal twelve-coordinate sign columns give the required parity clique. -/
module
public import EntropyQuadraticClassification.ParityKernels
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped BigOperators symmDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gf2Sign_mul : ∀ a b : ZMod 2,gf2Sign a*gf2Sign b=gf2Sign (a+b) := by decide

theorem twelve_balanced_support_card (hι : Fintype.card ι=12)
    (f : ι → ZMod 2) (hf : (∑ z,gf2Sign (f z))=0) :
    (oneSupport f).card=6 := by
  have h := gf2Sign_sum f
  rw [hf,hι] at h
  change 0=12-2*((oneSupport f).card : ℤ) at h
  omega

theorem twelve_orthogonal_intersection (hι : Fintype.card ι=12)
    (f g : ι → ZMod 2)
    (hf : (∑ z,gf2Sign (f z))=0) (hg : (∑ z,gf2Sign (g z))=0)
    (hfg : (∑ z,gf2Sign (f z)*gf2Sign (g z))=0) :
    (oneSupport f ∩ oneSupport g).card=3 := by
  have hadd : (∑ z,gf2Sign ((f+g) z))=0 := by
    simpa only [Pi.add_apply,←gf2Sign_mul] using hfg
  have hcf := twelve_balanced_support_card hι f hf
  have hcg := twelve_balanced_support_card hι g hg
  have hca := twelve_balanced_support_card hι (f+g) hadd
  rw [oneSupport_add] at hca
  have h := symmetric_difference_weight (oneSupport f) (oneSupport g)
  omega

theorem twelve_orthogonal_dot_odd (hι : Fintype.card ι=12)
    (f g : ι → ZMod 2)
    (hf : (∑ z,gf2Sign (f z))=0) (hg : (∑ z,gf2Sign (g z))=0)
    (hfg : (∑ z,gf2Sign (f z)*gf2Sign (g z))=0) :
    dotParity (oneSupport f) (oneSupport g)=1 := by
  unfold dotParity
  rw [twelve_orthogonal_intersection hι f g hf hg hfg]

end EntropyDesigns.QuadraticRefinement
