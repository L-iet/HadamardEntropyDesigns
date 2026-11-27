/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySpanningSlopes.RelativeCharacters
public import Mathlib.Tactic.LinearCombination
@[expose] public section
namespace EntropyDesigns.SpanningSlopes
noncomputable section
open SupportFace
open scoped BigOperators

def equalSeedIndices {k s : ℕ} (hs : s≠0) (t : Fin k → GaloisField 2 s)
    (p q : GaloisField 2 s × GaloisField 2 s) : Finset (Fin k) :=
  Finset.univ.filter (fun j => fieldSlopeSeeds hs t p j=fieldSlopeSeeds hs t q j)

theorem unequal_second_seed_at_most_one {k s : ℕ} (hs : s≠0)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t)
    (p q : GaloisField 2 s × GaloisField 2 s) (hb : p.2-q.2≠0) :
    (equalSeedIndices hs t p q).card≤1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hiEq := (Finset.mem_filter.mp hi).2
  have hjEq := (Finset.mem_filter.mp hj).2
  change fieldSeedEquiv s hs (p.1+t i*p.2)=fieldSeedEquiv s hs (q.1+t i*q.2) at hiEq
  change fieldSeedEquiv s hs (p.1+t j*p.2)=fieldSeedEquiv s hs (q.1+t j*q.2) at hjEq
  have h1 := (fieldSeedEquiv s hs).injective hiEq
  have h2 := (fieldSeedEquiv s hs).injective hjEq
  apply ht
  apply mul_right_cancel₀ hb
  linear_combination h1-h2

theorem equal_second_seed_no_equal_blocks {k s : ℕ} (hs : s≠0)
    (t : Fin k → GaloisField 2 s) (p q : GaloisField 2 s × GaloisField 2 s)
    (hb : p.2=q.2) (hpq : p≠q) : equalSeedIndices hs t p q=∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro j hj
  have he := (Finset.mem_filter.mp hj).2
  change fieldSeedEquiv s hs (p.1+t j*p.2)=fieldSeedEquiv s hs (q.1+t j*q.2) at he
  have h := (fieldSeedEquiv s hs).injective he
  rw [hb] at h
  exact hpq (Prod.ext (add_right_cancel h) hb)

theorem equalSeedIndices_sum {k s : ℕ} (hs : s≠0) (t : Fin k → GaloisField 2 s)
    (p q : GaloisField 2 s × GaloisField 2 s) :
    (∑ j : Fin k,if fieldSlopeSeeds hs t p j=fieldSlopeSeeds hs t q j then (1:ℤ) else 0)=
      (equalSeedIndices hs t p q).card := by
  classical
  rw [←Finset.sum_filter]
  simp [equalSeedIndices]

end
end EntropyDesigns.SpanningSlopes
