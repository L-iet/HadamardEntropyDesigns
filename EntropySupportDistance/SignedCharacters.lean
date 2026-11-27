/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.WalshBlock
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section

theorem signed_nonconstant_characters_unique {s : ℕ} (hs : 2≤s)
    (a b : Fin s → Bool) (sigma : ℤ) (hsigma : sigma=1 ∨ sigma= -1)
    (h : ∀ S : Finset (Fin s),S≠∅ → walshChar S b=sigma*walshChar S a) :
    sigma=1 ∧ a=b := by
  classical
  have hsingle (t : Fin s) : bitSign (b t)=sigma*bitSign (a t) := by
    simpa only [walshChar_singleton] using h {t} (Finset.singleton_ne_empty t)
  have hone : sigma=1 := by
    rcases hsigma with hpos|hneg
    · exact hpos
    · let i : Fin s := ⟨0,by omega⟩
      let j : Fin s := ⟨1,by omega⟩
      have hij : i≠j := by intro he;have hv := congrArg Fin.val he;change 0=1 at hv;omega
      have hp := h {i,j} (Finset.insert_ne_empty i {j})
      simp only [walshChar_pair i j hij] at hp
      rw [hsingle i,hsingle j,hneg] at hp
      rcases bitSign_sign (a i) with hi|hi <;>
        rcases bitSign_sign (a j) with hj|hj <;> norm_num [hi,hj] at hp
  refine ⟨hone,?_⟩
  funext t
  have ht := hsingle t
  rw [hone,one_mul] at ht
  cases ha : a t <;> cases hb : b t <;> simp_all [bitSign]

end
end EntropyDesigns.SupportFace
