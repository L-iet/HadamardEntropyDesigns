/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Coordinate supports connect binary linear codes to finite-set parity. -/
module
public import EntropyQuadraticClassification.Transvections
public import EntropyQuadraticClassification.AffineBalance
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped BigOperators symmDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def oneSupport (f : ι → ZMod 2) : Finset ι :=
  Finset.univ.filter (fun z => f z=1)

theorem gf2_sum_one_cases : ∀ a b : ZMod 2,
    a+b=1 ↔ (a=1 ∧ b≠1) ∨ (b=1 ∧ a≠1) := by decide

theorem gf2_sum_zero_cases : ∀ a b : ZMod 2,a+b=0 ↔ a=b := by decide

theorem binary_add_eq_zero_iff (f g : ι → ZMod 2) : f+g=0 ↔ f=g := by
  constructor
  · intro h
    funext z
    exact (gf2_sum_zero_cases (f z) (g z)).mp (congrFun h z)
  · intro h
    subst g
    funext z
    exact (gf2_sum_zero_cases (f z) (f z)).mpr rfl

theorem oneSupport_indicator (s : Finset ι) :
    oneSupport (fun z => if z∈s then (1 : ZMod 2) else 0)=s := by
  ext z
  by_cases h : z∈s <;> simp [oneSupport,h]

theorem oneSupport_injective : Function.Injective (oneSupport (ι:=ι)) := by
  intro f g h
  funext z
  have hm : f z=1 ↔ g z=1 := by
    simpa [oneSupport] using Finset.ext_iff.mp h z
  rcases gf2_two_cases (f z) with hf|hf <;>
    rcases gf2_two_cases (g z) with hg|hg <;> simp [hf,hg] at hm ⊢

theorem oneSupport_add (f g : ι → ZMod 2) :
    oneSupport (f+g)=oneSupport f ∆ oneSupport g := by
  ext z
  simp only [oneSupport,Pi.add_apply,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_symmDiff]
  exact gf2_sum_one_cases (f z) (g z)

theorem oneSupport_dot (f g : ι → ZMod 2) :
    (∑ z,f z*g z)=((oneSupport f ∩ oneSupport g).card : ZMod 2) := by
  classical
  have h : ∀ z,f z*g z=
      if z∈oneSupport f ∩ oneSupport g then (1 : ZMod 2) else 0 := by
    intro z
    rcases gf2_two_cases (f z) with hf|hf <;>
      rcases gf2_two_cases (g z) with hg|hg <;> simp [oneSupport,hf,hg]
  simp_rw [h]
  simp only [Finset.sum_boole]
  have he : Finset.univ.filter (fun z => z∈oneSupport f ∩ oneSupport g) = oneSupport f ∩ oneSupport g := by
    ext z
    simp
  rw [he]

theorem oneSupport_dot_zero (f g : ι → ZMod 2) (h : (∑ z,f z*g z)=0) :
    dotParity (oneSupport f) (oneSupport g)=0 := by
  have hc : ((oneSupport f ∩ oneSupport g).card : ZMod 2)=0 :=
    (oneSupport_dot f g).symm.trans h
  exact (ZMod.natCast_eq_natCast_iff' _ 0 2).mp hc

theorem oneSupport_dot_one (f g : ι → ZMod 2) (h : (∑ z,f z*g z)=1) :
    dotParity (oneSupport f) (oneSupport g)=1 := by
  have hc : ((oneSupport f ∩ oneSupport g).card : ZMod 2)=1 :=
    (oneSupport_dot f g).symm.trans h
  exact (ZMod.natCast_eq_natCast_iff' _ 1 2).mp hc

end EntropyDesigns.QuadraticRefinement
