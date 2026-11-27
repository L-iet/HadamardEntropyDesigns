/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.CompletionIntersection
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

theorem seedXor_left_injective {s : ℕ} (a : Fin s → Bool) :
    Function.Injective (seedXor a) := by
  intro c d h
  funext j
  have hj := congrFun h j
  cases ha : a j <;> cases hc : c j <;> cases hd : d j <;> simp_all [seedXor]

theorem hadamard_rows_injective {k : ℕ} (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) : Function.Injective K := by
  classical
  intro t u hrows
  by_contra hne
  have hoff := congrArg (fun M : Matrix (Fin k) (Fin k) ℤ => M t u) hK.mul_conjTranspose
  have hdiag := congrArg (fun M : Matrix (Fin k) (Fin k) ℤ => M u u) hK.mul_conjTranspose
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,Matrix.smul_apply,
    Matrix.one_apply,Fintype.card_fin,smul_eq_mul,hne,ite_false,mul_zero,ite_true,mul_one] at hoff hdiag
  have hsum : (∑ j,K t j*K u j)=(∑ j,K u j*K u j) := by rw [hrows]
  have hk : 0<k := by have hi := i0.isLt;omega
  have hkz : (0:ℤ)<k := by exact_mod_cast hk
  omega

theorem completed_rows_globally_injective {k s : ℕ} (hs : 2≤s)
    (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (c d : BlockSeeds k s) (hc : c i0=fun _ => false) (hd : d i0=fun _ => false)
    (t u : Fin k) (a b : Fin s → Bool)
    (heq : completedOffsetRow e i0 c (fun i j => K i j) t a=
      completedOffsetRow e i0 d (fun i j => K i j) u b) :
    c=d ∧ t=u ∧ a=b := by
  classical
  have hj (j : Fin k) : K t j=K u j ∧ offsetSeed c a j=offsetSeed d b j := by
    have ht := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hK.apply_mem t j)
    have hu := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hK.apply_mem u j)
    have hu2 : K u j*K u j=1 := by rcases hu with h|h <;> simp [h]
    have hsign : K u j*K t j=1 ∨ K u j*K t j= -1 := by
      rcases ht with h|h <;> rcases hu with h'|h' <;> simp [h,h']
    have hchars : ∀ S : Finset (Fin s),S≠∅ →
        walshChar S (offsetSeed d b j)=(K u j*K t j)*walshChar S (offsetSeed c a j) := by
      intro S hS
      have hraw := congrFun heq (j,S)
      change K t j*fullSourceRow e i0 (offsetSeed c a) (j,S)=
        K u j*fullSourceRow e i0 (offsetSeed d b) (j,S) at hraw
      simp only [fullSourceRow,hS,ite_false] at hraw
      calc
        _ = K u j*(K u j*walshChar S (offsetSeed d b j)) := by rw [←mul_assoc,hu2,one_mul]
        _ = K u j*(K t j*walshChar S (offsetSeed c a j)) := by rw [hraw]
        _ = _ := by ring
    obtain ⟨hsig,hseeds⟩ := signed_nonconstant_characters_unique hs
      (offsetSeed c a j) (offsetSeed d b j) (K u j*K t j) hsign hchars
    refine ⟨?_,hseeds⟩
    rcases ht with h|h <;> rcases hu with h'|h' <;> simp_all
  have hab : a=b := by
    have h := (hj i0).2
    change seedXor a (c i0)=seedXor b (d i0) at h
    rw [hc,hd] at h
    funext j
    have hv := congrFun h j
    cases ha : a j <;> cases hb : b j <;> simp_all [seedXor]
  refine ⟨?_,?_,hab⟩
  · funext j
    have h := (hj j).2
    change seedXor a (c j)=seedXor b (d j) at h
    rw [hab] at h
    exact seedXor_left_injective b h
  · apply hadamard_rows_injective i0 K hK
    funext j
    exact (hj j).1

end
end EntropyDesigns.SupportFace
