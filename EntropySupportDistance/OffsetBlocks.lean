/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SourceOffsets
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

theorem offset_block_inner {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (a b : Fin s → Bool) (j : Fin k) :
    (∑ S : Finset (Fin s),
      fullSourceRow e i0 (offsetSeed c a) (j,S)*fullSourceRow e i0 (offsetSeed c b) (j,S))=
      if a=b then (2:ℤ)^s else 0 := by
  classical
  have hc : ∀ v : Fin s → Bool,
      walshChar e (offsetSeed c v i0)*walshChar e (offsetSeed c v j)=
        walshChar e (c i0)*walshChar e (c j) := by
    intro v
    change walshChar e (seedXor v (c i0))*walshChar e (seedXor v (c j))=_
    rw [walshChar_seedXor,walshChar_seedXor]
    calc
      _ = (walshChar e v)^2*(walshChar e (c i0)*walshChar e (c j)) := by ring
      _ = _ := by rw [walshChar_sq,one_mul]
  have hp : (walshChar e (c i0)*walshChar e (c j))^2=1 := by
    rcases walshChar_sign e (c i0) with h|h <;>
      rcases walshChar_sign e (c j) with h'|h' <;> norm_num [h,h']
  have hterm (S : Finset (Fin s)) :
      fullSourceRow e i0 (offsetSeed c a) (j,S)*fullSourceRow e i0 (offsetSeed c b) (j,S)=
        walshChar S (offsetSeed c a j)*walshChar S (offsetSeed c b j) := by
    by_cases hS : S=∅
    · subst S
      simp only [fullSourceRow,ite_true,hc]
      simpa only [walshChar,Finset.prod_empty,mul_one,←pow_two,one_pow] using hp
    · simp only [fullSourceRow,hS,ite_false]
  simp_rw [hterm]
  rw [walshChar_dual_orthogonality]
  have heq : offsetSeed c a j=offsetSeed c b j ↔ a=b :=
    (seedXor_right_injective (c j)).eq_iff
  simp only [heq]

def completedOffsetRow {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Fin k → Fin k → ℤ) (t : Fin k) (a : Fin s → Bool) :
    Fin k × Finset (Fin s) → ℤ :=
  fun z => K t z.1*fullSourceRow e i0 (offsetSeed c a) z

theorem completedOffsetRow_inner {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Fin k → Fin k → ℤ) (t u : Fin k) (a b : Fin s → Bool) :
    (∑ j : Fin k,∑ S : Finset (Fin s),
      completedOffsetRow e i0 c K t a (j,S)*completedOffsetRow e i0 c K u b (j,S))=
      (if a=b then (2:ℤ)^s else 0)*(∑ j : Fin k,K t j*K u j) := by
  classical
  have hterm (j : Fin k) (S : Finset (Fin s)) :
      completedOffsetRow e i0 c K t a (j,S)*completedOffsetRow e i0 c K u b (j,S)=
        (K t j*K u j)*(fullSourceRow e i0 (offsetSeed c a) (j,S)*
          fullSourceRow e i0 (offsetSeed c b) (j,S)) := by
    unfold completedOffsetRow
    ring
  simp_rw [hterm,←Finset.mul_sum,offset_block_inner]
  rw [←Finset.sum_mul]
  ring

end
end EntropyDesigns.SupportFace
