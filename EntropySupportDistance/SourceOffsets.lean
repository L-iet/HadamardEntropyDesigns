/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SourceClique
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

def seedXor {s : ℕ} (a b : Fin s → Bool) : Fin s → Bool := fun t => Bool.xor (a t) (b t)

theorem seedXor_right_injective {s : ℕ} (c : Fin s → Bool) :
    Function.Injective (fun a => seedXor a c) := by
  intro a b hab
  funext t
  have ht := congrFun hab t
  cases ha : a t <;> cases hb : b t <;> cases hc : c t <;> simp_all [seedXor]

theorem walshChar_seedXor {s : ℕ} (S : Finset (Fin s)) (a b : Fin s → Bool) :
    walshChar S (seedXor a b)=walshChar S a*walshChar S b := by
  have h (t : Fin s) : bitSign (Bool.xor (a t) (b t))=bitSign (a t)*bitSign (b t) := by
    cases a t <;> cases b t <;> norm_num [bitSign]
  simp only [walshChar,seedXor,h,Finset.prod_mul_distrib]

def offsetSeed {k s : ℕ} (c : BlockSeeds k s) (a : Fin s → Bool) : BlockSeeds k s :=
  fun j => seedXor a (c j)

theorem offsetSeed_injective {k s : ℕ} (i0 : Fin k) (c : BlockSeeds k s) :
    Function.Injective (offsetSeed c) := by
  intro a b hab
  exact seedXor_right_injective (c i0) (congrFun hab i0)

theorem offset_relativeChar {k s : ℕ} (e : Finset (Fin s)) (c : BlockSeeds k s)
    (a b : Fin s → Bool) (j : Fin k) :
    relativeChar e (offsetSeed c a) (offsetSeed c b) j=walshChar e a*walshChar e b := by
  change (walshChar e (seedXor a (c j)))*(walshChar e (seedXor b (c j)))=_
  rw [walshChar_seedXor,walshChar_seedXor]
  have hs := walshChar_sq e (c j)
  calc
    _ = (walshChar e a*walshChar e b)*(walshChar e (c j))^2 := by ring
    _ = _ := by rw [hs,mul_one]

theorem offsetSeed_orthogonal {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (a b : Fin s → Bool) (hab : a≠b) :
    fullSourceInner e i0 (offsetSeed c a) (offsetSeed c b)=0 := by
  classical
  have hne (j : Fin k) : offsetSeed c a j≠offsetSeed c b j := by
    exact fun h => hab (seedXor_right_injective (c j) h)
  have hp : (walshChar e a*walshChar e b)*(walshChar e a*walshChar e b)=1 := by
    rcases walshChar_sign e a with h|h <;> rcases walshChar_sign e b with h'|h' <;> norm_num [h,h']
  rw [fullSourceInner_formula]
  simp only [hne,ite_false,Finset.sum_const_zero,mul_zero,offset_relativeChar,hp]
  simp

def offsetClique {k s : ℕ} (c : BlockSeeds k s) : Finset (BlockSeeds k s) :=
  Finset.univ.image (offsetSeed c)

theorem offsetClique_card {k s : ℕ} (i0 : Fin k) (c : BlockSeeds k s) :
    (offsetClique c).card=2^s := by
  classical
  rw [offsetClique,Finset.card_image_of_injective _ (offsetSeed_injective i0 c)]
  simp

theorem offsetClique_orthogonal {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) :
    ∀ x ∈ offsetClique c, ∀ y ∈ offsetClique c, x≠y → fullSourceInner e i0 x y=0 := by
  classical
  intro x hx y hy hne
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hy
  apply offsetSeed_orthogonal e i0 c a b
  exact fun h => hne (congrArg (offsetSeed c) h)

end
end EntropyDesigns.SupportFace
