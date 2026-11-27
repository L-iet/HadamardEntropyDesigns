/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Upper bounds for the original quadratic observables, using canonical clique estimates. -/
module
public import EntropyQuadraticClassification.QuadraticLowerFrames
public import Mathlib.Data.List.FinRange
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped symmDiff

theorem support_family_parity_clique {ι : Type*} [DecidableEq ι] {m : ℕ}
    (supports : Fin m → Finset ι)
    (hpair : ∀ i j,i≠j → (supports i ∩ supports j).card=3) :
    ((List.finRange m).map supports).Pairwise (fun s t => dotParity s t=1) := by
  apply List.pairwise_map.mpr
  have hn : (List.finRange m).Pairwise (fun i j => i≠j) := List.nodup_finRange m
  exact hn.imp (fun {i j} hij => by
    unfold dotParity
    rw [hpair i j hij])

theorem quadratic_single_check_upper (S : Finset (Finset (Fin 4))) (hS : S.card=12)
    (h : S → ZMod 2)
    (hh : h∈(binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))) (hh0 : h≠0)
    (hD : (binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))=
        Submodule.span (ZMod 2) {h})
    (hcanonical : CanonicalCliqueEstimate independentBlocks 7)
    {m : ℕ} (hframe : HasQuadraticObservableFrame S m) : m≤7 := by
  classical
  obtain ⟨supports,hmem,hcard,hinter⟩ := supports_of_quadratic_frame S hS hframe
  let M := oneSupport h
  have hM : M.card=8 := quadratic_dual_weight_eight S (twelve_labels_proper S hS) h hh hh0
  have hsize : Fintype.card S=12 := by simp [hS]
  have hL : ∀ s∈(List.finRange m).map supports,s.card%4=2 ∧ dotParity s M=0 := by
    intro s hs
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
    constructor
    · rw [hcard i]
    · have hd := (binary_single_check_kernel _ h hD _).mp (hmem i)
      rw [indicatorF2_support] at hd
      exact (dotParity_comm _ _).trans hd
  have hb := single_check_clique_upper hsize M hM hcanonical _ hL
    (support_family_parity_clique supports hinter)
  simpa only [List.length_map,List.length_finRange] using hb

theorem quadratic_two_check_upper (S : Finset (Finset (Fin 4))) (hS : S.card=12)
    (h g : S → ZMod 2)
    (hh : h∈(binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S)))
    (hg : g∈(binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S)))
    (hh0 : h≠0) (hg0 : g≠0) (hhg : h≠g)
    (hD : (binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))=
        Submodule.span (ZMod 2) {h,g})
    (hcanonical : CanonicalCliqueEstimate planeBlocks 5)
    {m : ℕ} (hframe : HasQuadraticObservableFrame S m) : m≤5 := by
  classical
  obtain ⟨supports,hmem,hcard,hinter⟩ := supports_of_quadratic_frame S hS hframe
  let D := (binaryFunctionDotForm S).orthogonal
    ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))
  let M := oneSupport h
  let N := oneSupport g
  have hproper := twelve_labels_proper S hS
  have hM : M.card=8 := quadratic_dual_weight_eight S hproper h hh hh0
  have hN : N.card=8 := quadratic_dual_weight_eight S hproper g hg hg0
  have hX : (M ∆ N).card=8 := by
    change (oneSupport h ∆ oneSupport g).card=8
    rw [←oneSupport_add]
    exact quadratic_dual_weight_eight S hproper (h+g) (D.add_mem hh hg)
      (fun he => hhg ((binary_add_eq_zero_iff h g).mp he))
  have hsize : Fintype.card S=12 := by simp [hS]
  have hL : ∀ s∈(List.finRange m).map supports,
      s.card%4=2 ∧ dotParity s M=0 ∧ dotParity s N=0 := by
    intro s hs
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
    have hd := (binary_two_check_kernel _ h g hD _).mp (hmem i)
    rw [indicatorF2_support] at hd
    refine ⟨?_,(dotParity_comm _ _).trans hd.1,(dotParity_comm _ _).trans hd.2⟩
    rw [hcard i]
  have hb := two_check_clique_upper hsize M N hM hN hX hcanonical _ hL
    (support_family_parity_clique supports hinter)
  simpa only [List.length_map,List.length_finRange] using hb

end EntropyDesigns.QuadraticRefinement
