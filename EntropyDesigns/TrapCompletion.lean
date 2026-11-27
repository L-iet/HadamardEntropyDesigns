module

public import EntropyDesigns.WalshBlocks

/-! # Completion of every maximum orthogonal subset of trap rows -/

@[expose] public section
namespace EntropyDesigns

noncomputable def trapRowIndices {s : ℕ} (e : Finset (Fin s))
    (H : Matrix (Finset (Fin s) ⊕ Finset (Fin s)) (Finset (Fin s) ⊕ Finset (Fin s)) ℝ) :
    Finset (Finset (Fin s) ⊕ Finset (Fin s)) := by
  classical
  exact Finset.univ.filter (fun i => ∃ u : (Fin s → Bool) × (Fin s → Bool),
    ∀ j, H i j = (trapRow e u j : ℝ))

theorem hadamard_trap_row_count_le {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (H : Matrix (Finset (Fin s) ⊕ Finset (Fin s)) (Finset (Fin s) ⊕ Finset (Fin s)) ℝ)
    (hH : Matrix.IsHadamard H) : (trapRowIndices e H).card ≤ 2 ^ s := by
  classical
  choose u hu using (fun i : trapRowIndices e H => (Finset.mem_filter.mp i.property).2)
  have hinner : ∀ i j : trapRowIndices e H, i ≠ j → trapInner e (u i) (u j) = 0 := by
    intro i j hij
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    have h := congrArg (fun M => M i.val j.val) hH.mul_conjTranspose
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply, Matrix.one_apply, ite_eq_right hne, smul_eq_mul, mul_zero] at h
    simp_rw [hu i, hu j] at h
    exact_mod_cast h
  have hinj : Function.Injective (fun i : trapRowIndices e H => (u i).1) := by
    intro i j hsame
    by_contra hne
    exact ((trapInner_zero_iff hs e _ _).mp (hinner i j hne)).1 hsame
  have hcard := Fintype.card_le_of_injective _ hinj
  simpa using hcard

theorem complete_maximum_trap_clique {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (S : Finset ((Fin s → Bool) × (Fin s → Bool))) (hS : trapOrthogonal e S)
    (hcard : S.card = 2 ^ s) :
    ∃ (H : Matrix (Finset (Fin s) ⊕ Finset (Fin s)) (Finset (Fin s) ⊕ Finset (Fin s)) ℝ)
      (rows : S ↪ (Finset (Fin s) ⊕ Finset (Fin s))), Matrix.IsHadamard H ∧
        (∀ u j, H (rows u) j = (trapRow e u.val j : ℝ)) ∧
        (trapRowIndices e H).card = 2 ^ s := by
  classical
  obtain ⟨π, c, hc, hgraph, hmem, hmixed⟩ := maximum_trap_clique_graph hs e S hS hcard
  let H := Matrix.fromBlocks walshSquare (permutedWalsh π c) walshSquare (-(permutedWalsh π c))
  have hH : Matrix.IsHadamard H :=
    two_block_hadamard _ _ (walshSquare_hadamard s) (permutedWalsh_hadamard π c hc)
  let rows : S ↪ (Finset (Fin s) ⊕ Finset (Fin s)) := {
    toFun u := Sum.inl (seedMask u.val.1)
    inj' := by
      intro u v h
      apply trap_clique_first_injective hs e S hS
      exact (maskSeedEquiv s).symm.injective (Sum.inl.inj h) }
  have hdecode (a : Fin s → Bool) : maskSeed (seedMask a) = a :=
    (maskSeedEquiv s).apply_symm_apply a
  have hret : ∀ u j, H (rows u) j = (trapRow e u.val j : ℝ) := by
    intro u j
    change H (Sum.inl (seedMask u.val.1)) j = (trapRow e u.val j : ℝ)
    cases j with
    | inl T => simp [H, Matrix.fromBlocks, walshSquare, trapRow, hdecode]
    | inr T =>
      have hπ : π u.val.1 = u.val.2 := (hgraph u.val u.property).symm
      have hmix : (trapMixed e u.val : ℝ) = (c : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) (hmixed u.val u.property)
      by_cases hT : T = ∅ <;>
        simp [H, Matrix.fromBlocks, permutedWalsh, trapRow, hT, hdecode, hπ, hmix]
  have hlower : S.card ≤ (trapRowIndices e H).card := by
    let f : S → trapRowIndices e H := fun u =>
      ⟨rows u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨u.val, hret u⟩⟩⟩
    have hf : Function.Injective f := by
      intro u v huv
      apply rows.injective
      exact congrArg Subtype.val huv
    simpa using Fintype.card_le_of_injective f hf
  have hupper := hadamard_trap_row_count_le hs e H hH
  exact ⟨H, rows, hH, hret, by omega⟩

theorem complete_maximum_trap_row_subset {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (U : Finset ((Finset (Fin s) ⊕ Finset (Fin s)) → ℤ))
    (hsubset : ∀ r ∈ U, ∃ u : (Fin s → Bool) × (Fin s → Bool), trapRow e u = r)
    (horth : ∀ r ∈ U, ∀ t ∈ U, r ≠ t → ∑ j, r j * t j = 0)
    (hcard : U.card = 2 ^ s) :
    ∃ (H : Matrix (Finset (Fin s) ⊕ Finset (Fin s)) (Finset (Fin s) ⊕ Finset (Fin s)) ℝ)
      (rows : U ↪ (Finset (Fin s) ⊕ Finset (Fin s))), Matrix.IsHadamard H ∧
        (∀ r j, H (rows r) j = (r.val j : ℝ)) ∧ (trapRowIndices e H).card = 2 ^ s := by
  classical
  let S := Finset.univ.filter (fun u : (Fin s → Bool) × (Fin s → Bool) => trapRow e u ∈ U)
  let f : S → U := fun u => ⟨trapRow e u.val, (Finset.mem_filter.mp u.property).2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      apply Subtype.ext
      exact trapRow_injective e (congrArg Subtype.val h)
    · intro r
      obtain ⟨u, hu⟩ := hsubset r.val r.property
      have hmem : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu ▸ r.property⟩
      refine ⟨⟨u, hmem⟩, ?_⟩
      exact Subtype.ext hu
  let eqv := Equiv.ofBijective f hf
  have hScard : S.card = 2 ^ s := by
    have h := Fintype.card_congr eqv
    simpa only [Fintype.card_coe, hcard] using h
  have hSorth : trapOrthogonal e S := by
    intro u hu v hv huv
    exact horth _ (Finset.mem_filter.mp hu).2 _ (Finset.mem_filter.mp hv).2
      (fun h => huv (trapRow_injective e h))
  obtain ⟨H, rowsS, hH, hret, hcount⟩ := complete_maximum_trap_clique hs e S hSorth hScard
  let rows := eqv.symm.toEmbedding.trans rowsS
  refine ⟨H, rows, hH, ?_, hcount⟩
  intro r j
  change H (rowsS (eqv.symm r)) j = (r.val j : ℝ)
  rw [hret]
  have hvalues : trapRow e (eqv.symm r).val = r.val :=
    congrArg Subtype.val (eqv.apply_symm_apply r)
  rw [hvalues]

end EntropyDesigns
