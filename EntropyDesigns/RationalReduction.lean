module

public import EntropyDesigns.OrderedFieldReduction

/-! # Rational reduction gives vertices of the real moment polytope -/

@[expose] public section
namespace EntropyDesigns

theorem rational_independent_columns_real {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] (A : Matrix ι α ℚ)
    (hlin : LinearIndependent ℚ A.col) :
    LinearIndependent ℝ (A.map (Rat.castHom ℝ)).col := by
  have hrow : LinearIndependent ℚ A.transpose.row := hlin
  have hrank : A.rank = Fintype.card α := by
    simpa only [Matrix.rank_transpose] using hrow.rank_matrix
  have hgram : (A.transpose * A).rank = Fintype.card α :=
    (Matrix.rank_transpose_mul_self A).trans hrank
  have hunit : IsUnit (A.transpose * A) := Matrix.mulVec_surjective_iff_isUnit.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hgram)
  have hdet : (A.transpose * A).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  have hdetR : ((A.transpose * A).map (Rat.castHom ℝ)).det ≠ 0 := by
    change ((Rat.castHom ℝ).mapMatrix (A.transpose * A)).det ≠ 0
    rw [← RingHom.map_det]
    change (((A.transpose * A).det : ℚ) : ℝ) ≠ 0
    exact_mod_cast hdet
  have hgramR : IsUnit ((A.map (Rat.castHom ℝ)).transpose * A.map (Rat.castHom ℝ)) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.map_mul (f := Rat.castHom ℝ)] at hdetR
    exact hdetR
  apply Matrix.mulVec_injective_iff.mp
  intro x y hxy
  apply Matrix.mulVec_injective_iff_isUnit.mpr hgramR
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]

noncomputable def realLaw {α : Type*} (p : α → ℚ) : α → ℝ := fun a => (p a : ℝ)

theorem rational_support_cast {α : Type*} [Fintype α] (p : α → ℚ) :
    activeSupport (realLaw p) = FieldReduction.activeSupport p := by
  classical
  ext a
  simp [activeSupport, FieldReduction.activeSupport, realLaw]

theorem rational_collision_cast {α : Type*} [Fintype α] (p : α → ℚ) :
    ((FieldReduction.collision p : ℚ) : ℝ) = collision (realLaw p) := by
  simp [FieldReduction.collision, collision, realLaw, Rat.cast_sum, Rat.cast_pow]

theorem rational_feasible_cast {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α ℚ) (b : ι → ℚ) (p : α → ℚ) (hp : FieldReduction.feasibleLaw A b p) :
    feasibleLaw (A.map (Rat.castHom ℝ)) (realLaw b) (realLaw p) := by
  refine ⟨fun a => ?_, ?_, ?_⟩
  · change (0 : ℝ) ≤ (p a : ℝ)
    exact_mod_cast hp.1 a
  · change (∑ a, (p a : ℝ)) = 1
    exact_mod_cast hp.2.1
  · funext i
    have h := congrFun hp.2.2 i
    change (∑ a, (A i a : ℝ) * (p a : ℝ)) = (b i : ℝ)
    change (∑ a, A i a * p a) = b i at h
    exact_mod_cast h

theorem rational_step_cast {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α ℚ) (b : ι → ℚ) (p q : α → ℚ)
    (hstep : FieldReduction.reductionStep A b p q) :
    reductionStep (A.map (Rat.castHom ℝ)) (realLaw b) (realLaw p) (realLaw q) := by
  refine ⟨rational_feasible_cast A b q hstep.1, ?_, ?_, ?_, ?_⟩
  · rw [← rational_collision_cast, ← rational_collision_cast]
    exact_mod_cast hstep.2.1
  · rw [rational_support_cast, rational_support_cast]
    exact hstep.2.2.1
  · rw [rational_support_cast, rational_support_cast]
    exact hstep.2.2.2.1
  · change 0 ≤ ∑ a, (p a : ℝ) * ((q a : ℝ) - (p a : ℝ))
    have h := hstep.2.2.2.2
    change 0 ≤ ∑ a, p a * (q a - p a) at h
    exact_mod_cast h

theorem rational_reduction_real_vertex {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℚ) (b : ι → ℚ) (p : α → ℚ)
    (hp : FieldReduction.feasibleLaw A b p) (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1) :
    ∃ k : ℕ, k ≤ (activeSupport (realLaw p)).card -
        ((A.map (Rat.castHom ℝ)).submatrix id
          (fun a : activeSupport (realLaw p) => (a : α))).rank ∧
      ∃ path : Fin (k + 1) → (α → ℚ),
        path ⟨0, Nat.zero_lt_succ k⟩ = p ∧
        (∀ j : Fin k, FieldReduction.reductionStep A b (path j.castSucc) (path j.succ)) ∧
        realLaw (path (Fin.last k)) ∈ Set.extremePoints ℝ
          {q | feasibleLaw (A.map (Rat.castHom ℝ)) (realLaw b) q} ∧
        (activeSupport (realLaw (path (Fin.last k)))).card ≤ Fintype.card ι := by
  classical
  obtain ⟨k, _, path, hfirst, hsteps, hlast, hlin⟩ :=
    FieldReduction.bounded_support_reduction A b p hp i₀ hconstant
  let AR := A.map (Rat.castHom ℝ)
  let pathR := fun j : Fin (k + 1) => realLaw (path j)
  let D := fun q : α → ℝ => (activeSupport q).card -
    (AR.submatrix id (fun a : activeSupport q => (a : α))).rank
  have hfirstR : pathR ⟨0, Nat.zero_lt_succ k⟩ = realLaw p := congrArg realLaw hfirst
  have hstepsR : ∀ j : Fin k, reductionStep AR (realLaw b)
      (pathR j.castSucc) (pathR j.succ) :=
    fun j => rational_step_cast A b _ _ (hsteps j)
  have hfeasibleR : ∀ j : Fin (k + 1), feasibleLaw AR (realLaw b) (pathR j) := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · change feasibleLaw AR (realLaw b) (pathR ⟨0, Nat.zero_lt_succ k⟩)
      rw [hfirstR]
      exact rational_feasible_cast A b p hp
    · exact (hstepsR j).1
  have hdrop : ∀ j : Fin k, D (pathR j.succ) < D (pathR j.castSucc) := by
    intro j
    exact support_dimension_strict_drop AR _ _
      ((hfeasibleR j.castSucc).2.2.trans (hfeasibleR j.succ).2.2.symm)
      (hstepsR j).2.2.1 (hstepsR j).2.2.2.1
  have htel : ∀ j : Fin (k + 1), D (pathR j) + j.val ≤ D (realLaw p) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      change D (pathR ⟨0, Nat.zero_lt_succ k⟩) + 0 ≤ D (realLaw p)
      rw [hfirstR]
      omega
    | succ j ih =>
      have h := hdrop j
      simp only [Fin.val_succ, Fin.val_castSucc] at *
      omega
  have hk : k ≤ D (realLaw p) := by
    have h := htel (Fin.last k)
    simp only [Fin.val_last] at h
    omega
  have hlinR : LinearIndependent ℝ
      (AR.submatrix id (fun a : activeSupport (pathR (Fin.last k)) => (a : α))).col := by
    have hcast := rational_independent_columns_real
      (A.submatrix id (fun a : FieldReduction.activeSupport (path (Fin.last k)) => (a : α))) hlin
    let e : activeSupport (pathR (Fin.last k)) ≃ FieldReduction.activeSupport (path (Fin.last k)) :=
      Equiv.subtypeEquivRight (fun a => by
        simp [pathR, activeSupport, FieldReduction.activeSupport, realLaw])
    have hcomp := hcast.comp e e.injective
    have heq :
        (AR.submatrix id (fun a : activeSupport (pathR (Fin.last k)) => (a : α))).col =
          ((A.submatrix id
            (fun a : FieldReduction.activeSupport (path (Fin.last k)) => (a : α))).map
              (Rat.castHom ℝ)).col ∘ e := by
      funext a i
      rfl
    rw [heq]
    exact hcomp
  exact ⟨k, hk, path, hfirst, hsteps,
    independent_support_vertex AR (realLaw b) _ (hfeasibleR (Fin.last k)) hlinR,
    independent_support_card_bound AR _ hlinR⟩

end EntropyDesigns
