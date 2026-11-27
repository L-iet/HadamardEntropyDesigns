/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPlotkinSupport.GroupBound
@[expose] public section
namespace EntropyDesigns.PlotkinSupport
noncomputable section
open SupportFace
open scoped BigOperators

theorem seed_clique_plotkin_bound {k s : ℕ} (hk : k≤2^s)
    (e : Finset (Fin s)) (i0 : Fin k) (T : Finset (BlockSeeds k s))
    (horth : ∀ x∈T,∀ y∈T,x≠y → fullSourceInner e i0 x y=0) :
    T.card≤2^s*(2^s/(2^s-k+1)) := by
  classical
  have hcount := Finset.card_eq_sum_card_fiberwise
    (f:=fun x : BlockSeeds k s => x i0) (s:=T) (t:=Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  calc
    T.card=∑ a : Fin s → Bool,(T.filter (fun x => x i0=a)).card := hcount
    _≤∑ _a : Fin s → Bool,2^s/(2^s-k+1) := by
      apply Finset.sum_le_sum
      intro a _
      apply shared_seed_group_bound hk e i0 a
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
      · intro x hx y hy hne
        exact horth x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne
    _=2^s*(2^s/(2^s-k+1)) := by simp

theorem observed_clique_plotkin_bound {k s : ℕ} (hk : k≤2^s)
    (e : Finset (Fin s)) (i0 : Fin k) (T : Finset (SourceOutcome k s i0))
    (hsub : T⊆observedSupport e i0) (horth : SupportWitness.IsClique observedOrthogonal T) :
    T.card≤2^s*(2^s/(2^s-k+1)) := by
  classical
  let U : Finset (BlockSeeds k s) := Finset.univ.filter (fun x => sourceCode e i0 x∈T)
  have himage : U.image (sourceCode e i0)=T := by
    ext y
    constructor
    · intro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hx).2
    · intro hy
      obtain ⟨x,_,hx⟩ := Finset.mem_image.mp (hsub hy)
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ x,by rw [hx];exact hy⟩,hx⟩
  have hUorth : ∀ x∈U,∀ y∈U,x≠y → fullSourceInner e i0 x y=0 := by
    intro x hx y hy hne
    apply (observed_orthogonal_iff e i0 x y).mp
    apply horth _ (Finset.mem_filter.mp hx).2 _ (Finset.mem_filter.mp hy).2
    exact fun heq => hne (sourceCode_injective e i0 heq)
  have hcard : U.card=T.card := by
    rw [←himage,Finset.card_image_of_injective _ (sourceCode_injective e i0)]
  rw [←hcard]
  exact seed_clique_plotkin_bound hk e i0 U hUorth

theorem observed_orthogonality_plotkin_bound {k s : ℕ} (hk : k≤2^s)
    (e : Finset (Fin s)) (i0 : Fin k) :
    SupportWitness.orthogonalityNumber observedOrthogonal (observedSupport e i0)≤
      2^s*(2^s/(2^s-k+1)) := by
  classical
  unfold SupportWitness.orthogonalityNumber
  apply Finset.sup_le
  intro T hT
  split_ifs with horth
  · exact observed_clique_plotkin_bound hk e i0 T (Finset.mem_powerset.mp hT) horth
  · exact Nat.zero_le _

end
end EntropyDesigns.PlotkinSupport
