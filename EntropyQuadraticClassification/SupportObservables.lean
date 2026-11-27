/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Balanced support families with intersection three give actual unbiased independent sign observables. -/
module
public import EntropyQuadraticClassification.ObservableSupports
public import EntropySupport.PuncturedObservables
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped BigOperators symmDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def indicatorF2 (s : Finset ι) (x : ι) : ZMod 2 := if x∈s then 1 else 0

theorem indicatorF2_support (s : Finset ι) : oneSupport (indicatorF2 s)=s :=
  oneSupport_indicator s

theorem indicatorF2_sign (s : Finset ι) (x : ι) :
    gf2Sign (indicatorF2 s x)=bitSign (decide (x∈s)) := by
  by_cases hx : x∈s <;> simp [indicatorF2,gf2Sign,bitSign,hx]

theorem indicatorF2_balanced (hι : Fintype.card ι=12)
    (s : Finset ι) (hs : s.card=6) : (∑ x,gf2Sign (indicatorF2 s x))=0 := by
  have h := gf2Sign_sum (indicatorF2 s)
  change (∑ x,gf2Sign (indicatorF2 s x))=(Fintype.card ι : ℤ)-
    2*((oneSupport (indicatorF2 s)).card : ℤ) at h
  rw [h,indicatorF2_support,hs,hι]
  norm_num

theorem indicatorF2_orthogonal (hι : Fintype.card ι=12)
    (s t : Finset ι) (hs : s.card=6) (ht : t.card=6) (hst : (s ∩ t).card=3) :
    (∑ x,gf2Sign (indicatorF2 s x)*gf2Sign (indicatorF2 t x))=0 := by
  have hw := symmetric_difference_weight s t
  have hxor : (s ∆ t).card=6 := by omega
  have hcard : (oneSupport (indicatorF2 s+indicatorF2 t)).card=6 := by
    rw [oneSupport_add,indicatorF2_support,indicatorF2_support,hxor]
  have h := gf2Sign_sum (indicatorF2 s+indicatorF2 t)
  change (∑ x,gf2Sign ((indicatorF2 s+indicatorF2 t) x))=(Fintype.card ι : ℤ)-
    2*((oneSupport (indicatorF2 s+indicatorF2 t)).card : ℤ) at h
  rw [hι,hcard] at h
  norm_num at h
  simpa only [Pi.add_apply,←gf2Sign_mul] using h

theorem support_frame_uniform {m : ℕ} (hι : Fintype.card ι=12)
    (supports : Fin m → Finset ι)
    (hcard : ∀ i,(supports i).card=6)
    (hinter : ∀ i j,i≠j → (supports i ∩ supports j).card=3) :
    IsUniformBinaryPairwiseIndependent (fun x i => decide (x∈supports i)) := by
  constructor
  · intro i
    simpa only [indicatorF2_sign] using indicatorF2_balanced hι (supports i) (hcard i)
  · intro i j hij
    simpa only [indicatorF2_sign] using
      indicatorF2_orthogonal hι (supports i) (supports j) (hcard i) (hcard j) (hinter i j hij)

end EntropyDesigns.QuadraticRefinement
