/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.SourceCode
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

theorem card_nonzero_masks (s : ℕ) : Fintype.card (NonzeroMask s)=2^s-1 := by
  classical
  change Fintype.card {S : Finset (Fin s) // ¬ S=∅}=_
  rw [Fintype.card_subtype_compl]
  simp

theorem card_mixed_blocks {k : ℕ} (i0 : Fin k) : Fintype.card (MixedBlock k i0)=k-1 := by
  classical
  change Fintype.card {j : Fin k // ¬ j=i0}=_
  rw [Fintype.card_subtype_compl]
  simp

theorem card_source_coordinates {k : ℕ} (s : ℕ) (i0 : Fin k) :
    Fintype.card (SourceCoordinate k s i0)=k*(2^s)-1 := by
  classical
  simp only [SourceCoordinate,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    card_nonzero_masks,card_mixed_blocks,Nat.mul_sub_left_distrib,mul_one]
  have hk : 0<k := Nat.zero_lt_of_lt i0.isLt
  have hp : 1≤2^s := by have h : (0:ℕ)<2^s := pow_pos (by decide) s;omega
  have hm : k≤k*2^s := by simpa using Nat.mul_le_mul_left k hp
  omega

theorem source_pullback_collision {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (q : SourceOutcome k s i0 → ℝ) (hsupport : sourceSupported e i0 q) :
    collision q=collision (sourcePullback e i0 q) := by
  classical
  have h := pushLaw_injective_collision (sourceCode e i0) (sourceCode_injective e i0) (sourcePullback e i0 q)
  rw [source_push_pullback e i0 q hsupport] at h
  exact h

theorem source_collision_upper {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (q : SourceOutcome k s i0 → ℝ) (hq : sourceFeasible i0 q) (hsupport : sourceSupported e i0 q) :
    (∀ y,q y≤1/((2:ℝ)^s)^2) ∧ collision q≤1/((2:ℝ)^s)^2 := by
  classical
  let w := sourcePullback e i0 q
  obtain ⟨hw,hmass,hmom⟩ := source_pullback_moments e i0 q hq hsupport
  let i : Fin k := ⟨0,by omega⟩
  let j : Fin k := ⟨1,by omega⟩
  have hij : i≠j := by intro h;have hv := congrArg Fin.val h;dsimp [i,j] at hv;omega
  have hcap := block_atom_cap w hw hmass hmom i j hij
  refine ⟨?_,?_⟩
  · intro y
    by_cases hy : ∃ x,sourceCode e i0 x=y
    · obtain ⟨x,rfl⟩ := hy
      exact hcap x
    · rw [hsupport y hy]
      exact one_div_nonneg.mpr (sq_nonneg _)
  · rw [source_pullback_collision e i0 q hsupport]
    exact block_collision_cap hk w hw hmass hmom

theorem source_active_seed_equiv {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (q : SourceOutcome k s i0 → ℝ) (hsupport : sourceSupported e i0 q) :
    Nonempty ({x : BlockSeeds k s // sourcePullback e i0 q x≠0} ≃
      {y : SourceOutcome k s i0 // q y≠0}) := by
  classical
  let f : {x : BlockSeeds k s // sourcePullback e i0 q x≠0} →
      {y : SourceOutcome k s i0 // q y≠0} := fun x => ⟨sourceCode e i0 x.val,x.property⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact sourceCode_injective e i0 (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    intro y
    have hex : ∃ x,sourceCode e i0 x=y.val := by
      by_contra h
      exact y.property (hsupport y.val h)
    obtain ⟨x,hx⟩ := hex
    have hwx : sourcePullback e i0 q x≠0 := by change q (sourceCode e i0 x)≠0;rw [hx];exact y.property
    refine ⟨⟨x,hwx⟩,?_⟩
    apply Subtype.ext
    exact hx
  exact ⟨Equiv.ofBijective f ⟨hinj,hsurj⟩⟩

theorem source_collision_equality_oa {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (q : SourceOutcome k s i0 → ℝ) (hq : sourceFeasible i0 q) (hsupport : sourceSupported e i0 q)
    (heq : collision q=1/((2:ℝ)^s)^2) :
    (∀ y,q y=0 ∨ q y=1/((2:ℝ)^s)^2) ∧
    Nat.card {y : SourceOutcome k s i0 // q y≠0}=(2^s)^2 ∧
    (∀ i j : Fin k,i≠j → Function.Bijective
      (fun x : {x : BlockSeeds k s // sourcePullback e i0 q x≠0} => (x.val i,x.val j))) := by
  classical
  let w := sourcePullback e i0 q
  obtain ⟨hw,hmass,hmom⟩ := source_pullback_moments e i0 q hq hsupport
  have heqw : collision w=1/((2:ℝ)^s)^2 := (source_pullback_collision e i0 q hsupport).symm.trans heq
  obtain ⟨hweights,hbij,hcard⟩ := block_collision_equality_oa hk w hw hmass hmom heqw
  refine ⟨?_,?_,hbij⟩
  · intro y
    by_cases hy : ∃ x,sourceCode e i0 x=y
    · obtain ⟨x,rfl⟩ := hy;exact hweights x
    · exact Or.inl (hsupport y hy)
  · obtain ⟨eqv⟩ := source_active_seed_equiv e i0 q hsupport
    exact (Nat.card_congr eqv).symm.trans hcard
end
end EntropyDesigns.SupportFace
