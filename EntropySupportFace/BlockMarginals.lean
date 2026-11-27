/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.PairWalsh
public import EntropySupportFace.FiberRigidity
public import EntropyDesigns.Collision
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators
abbrev BlockSeeds (k s : ℕ) := Fin k → (Fin s → Bool)
def blockCharacterMoments {k s : ℕ} (w : BlockSeeds k s → ℝ) : Prop :=
  (∀ i S,S≠∅ → (∑ x,w x*(walshChar S (x i):ℝ))=0) ∧
  (∀ i j,i≠j → ∀ S T,S≠∅ → T≠∅ →
    (∑ x,w x*(walshChar S (x i):ℝ)*(walshChar T (x j):ℝ))=0)

theorem block_pair_coefficients {k s : ℕ} (w : BlockSeeds k s → ℝ)
    (hmass : ∑ x,w x=1) (hmom : blockCharacterMoments w) (i j : Fin k) (hij : i≠j) :
    ∀ P : PairMask s,pairCoefficient (pushLaw (fun x => (x i,x j)) w) P=
      if P=(∅,∅) then 1 else 0 := by
  classical
  intro P
  let f : BlockSeeds k s → PairSeed s := fun x => (x i,x j)
  have hp := pushLaw_moment (α:=BlockSeeds k s) (β:=PairSeed s) f w (pairChar P)
  change (∑ b : PairSeed s,pushLaw f w b*pairChar P b)=_
  rw [hp]
  change (∑ x : BlockSeeds k s,w x*pairChar P (x i,x j))=_
  rcases P with ⟨S,T⟩
  by_cases hS : S=∅ <;> by_cases hT : T=∅
  · subst S;subst T;simpa [pairChar,walshChar] using hmass
  · subst S;simpa [pairChar,walshChar,hT] using hmom.1 j T hT
  · subst T;simpa [pairChar,walshChar,hS] using hmom.1 i S hS
  · simpa [pairChar,hS,hT,mul_assoc] using hmom.2 i j hij S T hS hT

theorem block_pair_uniform {k s : ℕ} (w : BlockSeeds k s → ℝ)
    (hmass : ∑ x,w x=1) (hmom : blockCharacterMoments w) (i j : Fin k) (hij : i≠j) :
    ∀ b : PairSeed s,pushLaw (fun x => (x i,x j)) w b=1/((2:ℝ)^s)^2 :=
  pair_uniform_of_coefficients _ (block_pair_coefficients w hmass hmom i j hij)

theorem block_atom_cap {k s : ℕ} (w : BlockSeeds k s → ℝ) (hw : ∀ x,0≤w x)
    (hmass : ∑ x,w x=1) (hmom : blockCharacterMoments w) (i j : Fin k) (hij : i≠j) :
    ∀ x,w x≤1/((2:ℝ)^s)^2 := by
  classical
  intro x
  have hn (y : BlockSeeds k s) : 0 ≤ (if (y i,y j)=(x i,x j) then w y else 0) := by
    split
    · exact hw y
    · exact le_rfl
  have hs := Finset.single_le_sum (fun y (_ : y∈Finset.univ) => hn y) (Finset.mem_univ x)
  have hle : w x≤pushLaw (fun x => (x i,x j)) w (x i,x j) := by simpa [pushLaw] using hs
  rw [block_pair_uniform w hmass hmom i j hij (x i,x j)] at hle
  exact hle

theorem block_collision_cap {k s : ℕ} (hk : 2≤k) (w : BlockSeeds k s → ℝ)
    (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1) (hmom : blockCharacterMoments w) :
    collision w≤1/((2:ℝ)^s)^2 := by
  let i : Fin k := ⟨0,by omega⟩
  let j : Fin k := ⟨1,by omega⟩
  have hij : i≠j := by intro h;have hv := congrArg Fin.val h;dsimp [i,j] at hv;omega
  exact collision_le_of_atom_bound w _ hw hmass (block_atom_cap w hw hmass hmom i j hij)

theorem block_collision_equality_oa {k s : ℕ} (hk : 2≤k) (w : BlockSeeds k s → ℝ)
    (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1) (hmom : blockCharacterMoments w)
    (heq : collision w=1/((2:ℝ)^s)^2) :
    (∀ x,w x=0 ∨ w x=1/((2:ℝ)^s)^2) ∧
    (∀ i j : Fin k,i≠j → Function.Bijective (fun x : {x : BlockSeeds k s // w x≠0} => (x.val i,x.val j))) ∧
    Nat.card {x : BlockSeeds k s // w x≠0}=(2^s)^2 := by
  classical
  let i : Fin k := ⟨0,by omega⟩
  let j : Fin k := ⟨1,by omega⟩
  have hij : i≠j := by intro h;have hv := congrArg Fin.val h;dsimp [i,j] at hv;omega
  have hcap := block_atom_cap w hw hmass hmom i j hij
  have hweights := equality_forces_capped_weights w _ hw hmass hcap heq
  have hc : 0<1/((2:ℝ)^s)^2 := one_div_pos.mpr (sq_pos_of_pos (pow_pos (by norm_num) _))
  have hbij (a b : Fin k) (hab : a≠b) :
      Function.Bijective (fun x : {x : BlockSeeds k s // w x≠0} => (x.val a,x.val b)) :=
    uniform_fiber_active_bijective _ w _ hc hw hweights (block_pair_uniform w hmass hmom a b hab)
  refine ⟨hweights,hbij,?_⟩
  let e := Equiv.ofBijective _ (hbij i j hij)
  calc
    Nat.card {x : BlockSeeds k s // w x≠0}=Nat.card (PairSeed s) := Nat.card_congr e
    _=(2^s)^2 := by simp [PairSeed,Nat.card_eq_fintype_card,pow_two]
end
end EntropyDesigns.SupportFace
