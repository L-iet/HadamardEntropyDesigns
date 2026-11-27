/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Construct actual quadratic observable frames on arbitrary twelve-label sets from their dual check type. -/
module
public import EntropyQuadraticClassification.FrameSupportEquivalence
public import EntropyQuadraticClassification.ArbitraryCheckUpper
public import EntropyQuadraticClassification.SupportPullback
public import EntropyQuadraticClassification.BlockWitnesses
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped symmDiff

theorem twelve_labels_proper (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    S≠Finset.univ := by
  intro he
  have hc := congrArg Finset.card he
  have hu : (Finset.univ : Finset (Finset (Fin 4))).card=16 := by decide
  rw [hS,hu] at hc
  omega

theorem quadratic_single_check_frame (S : Finset (Finset (Fin 4))) (hS : S.card=12)
    (h : S → ZMod 2)
    (hh : h∈(binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))) (hh0 : h≠0)
    (hD : (binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))=
        Submodule.span (ZMod 2) {h}) : HasQuadraticObservableFrame S 7 := by
  classical
  let M := oneSupport h
  have hsize : Fintype.card S=12 := by simp [hS]
  have hM : M.card=8 := quadratic_dual_weight_eight S (twelve_labels_proper S hS) h hh hh0
  obtain ⟨e,heM,heComp⟩ := eight_four_partition_equiv hsize M hM
  let supports : Fin 7 → Finset S := fun i =>
    (encodedSupport (independentBalancedWord i)).map e.symm.toEmbedding
  apply quadratic_frame_of_supports S hS supports
  · intro i
    apply (binary_single_check_kernel _ h hD _).mpr
    rw [indicatorF2_support]
    change dotParity M ((encodedSupport (independentBalancedWord i)).map e.symm.toEmbedding)=0
    rw [support_dot_pullback,heM,dotParity_comm]
    exact (blockChecks_iff _ _).mp (independentWitness_checks i)
      (encodedSupport 255,0) (by simp [independentBlocks])
  · intro i
    exact (support_map_card e.symm _).trans (independentWitness_card i)
  · intro i j hij
    change ((encodedSupport (independentBalancedWord i)).map e.symm.toEmbedding ∩
      (encodedSupport (independentBalancedWord j)).map e.symm.toEmbedding).card=3
    rw [←Finset.map_inter,Finset.card_map]
    exact independentWitness_intersection i j hij

theorem quadratic_two_check_frame (S : Finset (Finset (Fin 4))) (hS : S.card=12)
    (h g : S → ZMod 2)
    (hh : h∈(binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S)))
    (hg : g∈(binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S)))
    (hh0 : h≠0) (hg0 : g≠0) (hhg : h≠g)
    (hD : (binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))=
        Submodule.span (ZMod 2) {h,g}) : HasQuadraticObservableFrame S 5 := by
  classical
  let D := (binaryFunctionDotForm S).orthogonal
    ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))
  let M := oneSupport h
  let N := oneSupport g
  have hproper := twelve_labels_proper S hS
  have hsize : Fintype.card S=12 := by simp [hS]
  have hM : M.card=8 := quadratic_dual_weight_eight S hproper h hh hh0
  have hN : N.card=8 := quadratic_dual_weight_eight S hproper g hg hg0
  have hX : (M ∆ N).card=8 := by
    change (oneSupport h ∆ oneSupport g).card=8
    rw [←oneSupport_add]
    exact quadratic_dual_weight_eight S hproper (h+g) (D.add_mem hh hg)
      (fun he => hhg ((binary_add_eq_zero_iff h g).mp he))
  have hcover := weight_eight_covers hsize M N hM hN hX
  obtain ⟨e,heA,heComp,heC⟩ := three_four_partition_equiv hsize M N hM hN hX
  let word : Fin 5 → ℕ := fun i => balancedWitnessWord (Fin.castLE (by decide : 5≤7) i)
  let supports : Fin 5 → Finset S := fun i => (encodedSupport (word i)).map e.symm.toEmbedding
  have hMdecomp : M=(M \ N) ∆ (M ∩ N) := by
    ext x
    simp only [Finset.mem_symmDiff,Finset.mem_sdiff,Finset.mem_inter]
    tauto
  have hNdecomp : N=(Finset.univ \ M) ∆ (M ∩ N) := by
    ext x
    have hc : x∈M ∨ x∈N := by
      have hx : x∈M ∪ N := by rw [hcover]; exact Finset.mem_univ x
      exact Finset.mem_union.mp hx
    simp only [Finset.mem_symmDiff,Finset.mem_sdiff,Finset.mem_inter,Finset.mem_univ]
    tauto
  apply quadratic_frame_of_supports S hS supports
  · intro i
    have hchecks := (blockChecks_iff _ _).mp (planeWitness_checks i)
    have hA : dotParity (M \ N) (supports i)=0 := by
      change dotParity (M \ N) ((encodedSupport (word i)).map e.symm.toEmbedding)=0
      rw [support_dot_pullback,heA,dotParity_comm]
      exact hchecks (encodedSupport 15,0) (by simp [planeBlocks])
    have hB : dotParity (Finset.univ \ M) (supports i)=0 := by
      change dotParity (Finset.univ \ M) ((encodedSupport (word i)).map e.symm.toEmbedding)=0
      rw [support_dot_pullback,heComp,dotParity_comm]
      exact hchecks (encodedSupport 240,4) (by simp [planeBlocks])
    have hC : dotParity (M ∩ N) (supports i)=0 := by
      change dotParity (M ∩ N) ((encodedSupport (word i)).map e.symm.toEmbedding)=0
      rw [support_dot_pullback,heC,dotParity_comm]
      exact hchecks (encodedSupport 3840,8) (by simp [planeBlocks])
    apply (binary_two_check_kernel _ h g hD _).mpr
    rw [indicatorF2_support]
    constructor
    · change dotParity M (supports i)=0
      rw [hMdecomp,dotParity_xor_left,hA,hC]
    · change dotParity N (supports i)=0
      rw [hNdecomp,dotParity_xor_left,hB,hC]
  · intro i
    exact (support_map_card e.symm _).trans (planeWitness_card i)
  · intro i j hij
    change ((encodedSupport (word i)).map e.symm.toEmbedding ∩
      (encodedSupport (word j)).map e.symm.toEmbedding).card=3
    rw [←Finset.map_inter,Finset.card_map]
    exact planeWitness_intersection i j hij

end EntropyDesigns.QuadraticRefinement
