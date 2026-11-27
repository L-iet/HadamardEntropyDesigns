module

public import EntropyDesigns.Pushforward
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Basic.Real.Star

/-! # Probability laws obtained by retaining Hadamard coordinates -/

@[expose] public section
namespace EntropyDesigns

/-- Two orthogonal sign rows cannot agree on a strict majority of coordinates. -/
theorem orthogonal_sign_rows_separated_on_majority {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (u v : ι → ℝ) (hu : ∀ i, u i = 1 ∨ u i = -1)
    (hv : ∀ i, v i = 1 ∨ v i = -1)
    (horth : ∑ i, u i * v i = 0) (s : Finset ι)
    (hcard : Fintype.card ι < 2 * s.card) :
    ∃ i ∈ s, u i ≠ v i := by
  by_contra h
  push Not at h
  have hterm : ∀ i, 2 * (if i ∈ s then (1 : ℝ) else 0) - 1 ≤ u i * v i := by
    intro i
    by_cases hi : i ∈ s
    · rw [h i hi]
      rcases hv i with hx | hx <;> norm_num [hi, hx]
    · rcases hu i with hx | hx <;> rcases hv i with hy | hy <;> simp [hi, hx, hy]
  have hbound := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hterm i)
  rw [horth] at hbound
  have hindicator : (∑ i : ι, if i ∈ s then (1 : ℝ) else 0) = s.card := by simp
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hindicator] at hbound
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hbound
  have hc : (Fintype.card ι : ℝ) < 2 * (s.card : ℝ) := by exact_mod_cast hcard
  linarith

/-- Any Hadamard matrix at the rounded order supplies an actual Boolean-cube
law attaining the sharp collision and both entropy bounds. -/
theorem cube_law_of_hadamard {d : ℕ} (hd : 2 ≤ d)
    (H : Matrix (Fin (roundedDimension (d + 1))) (Fin (roundedDimension (d + 1))) ℝ)
    (hH : Matrix.IsHadamard H) :
    ∃ w : (Fin d → Bool) → ℝ,
      (∀ b, 0 ≤ w b) ∧ (∑ b, w b = 1) ∧
      (∀ i, ∑ b, w b * (bitSign (b i) : ℝ) = 0) ∧
      (∀ i j, i ≠ j →
        ∑ b, w b * (bitSign (b i) : ℝ) * (bitSign (b j) : ℝ) = 0) ∧
      collision w = 1 / (roundedDimension (d + 1) : ℝ) ∧
      collisionEntropy w = Real.log (roundedDimension (d + 1)) ∧
      shannon w = Real.log (roundedDimension (d + 1)) := by
  classical
  let N := roundedDimension (d + 1)
  have hle : d + 1 ≤ N := by dsimp [N, roundedDimension]; omega
  have hmajor : N < 2 * (d + 1) := by dsimp [N, roundedDimension]; omega
  let J : Fin (d + 1) ↪ Fin N :=
    ⟨Fin.castLE hle, fun _ _ h => Fin.ext (congrArg (fun k : Fin N => k.val) h)⟩
  let j₀ := J 0
  have hsign : ∀ a j, H a j = 1 ∨ H a j = -1 :=
    fun a j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem a j)
  have hsquare : ∀ a, H a j₀ ^ 2 = 1 := by
    intro a
    rcases hsign a j₀ with h | h <;> simp [h]
  let x : Fin N → Fin d → ℤ :=
    fun a i => if H a j₀ * H a (J i.succ) = 1 then 1 else -1
  have hxsign : ∀ a i, x a i = 1 ∨ x a i = -1 := by
    intro a i
    dsimp [x]
    split_ifs <;> simp
  have hvalue : ∀ a i, (x a i : ℝ) = H a j₀ * H a (J i.succ) := by
    intro a i
    rcases hsign a j₀ with h | h <;>
      rcases hsign a (J i.succ) with h' | h' <;> norm_num [x, h, h']
  have hmean : ∀ i, ∑ a, (x a i : ℝ) = 0 := by
    intro i
    simp_rw [hvalue]
    have hne : j₀ ≠ J i.succ := by
      intro h
      have : (0 : Fin (d + 1)) = i.succ := J.injective h
      exact (Fin.succ_ne_zero i) this.symm
    have hc := congrArg (fun M => M j₀ (J i.succ)) hH.conjTranspose_mul
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, hne, ite_false, mul_zero] using hc
  have hpair : ∀ i j, i ≠ j → ∑ a, (x a i : ℝ) * (x a j : ℝ) = 0 := by
    intro i j hij
    have hne : J i.succ ≠ J j.succ := by
      intro h
      apply hij
      exact Fin.ext (Nat.succ.inj (congrArg (fun k : Fin (d + 1) => k.val) (J.injective h)))
    calc
      ∑ a, (x a i : ℝ) * (x a j : ℝ) =
          ∑ a, H a (J i.succ) * H a (J j.succ) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [hvalue, hvalue]
        calc
          _ = H a j₀ ^ 2 * (H a (J i.succ) * H a (J j.succ)) := by ring
          _ = _ := by rw [hsquare, one_mul]
      _ = 0 := by
        have hc := congrArg (fun M => M (J i.succ) (J j.succ)) hH.conjTranspose_mul
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
          Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
          Matrix.one_apply, smul_eq_mul, hne, ite_false, mul_zero] using hc
  have hinj : Function.Injective x := by
    intro a b hab
    by_contra hne
    let u := fun j => H a j₀ * H a j
    let v := fun j => H b j₀ * H b j
    have hu : ∀ j, u j = 1 ∨ u j = -1 := by
      intro j
      rcases hsign a j₀ with h | h <;> rcases hsign a j with h' | h' <;> simp [u,h,h']
    have hv : ∀ j, v j = 1 ∨ v j = -1 := by
      intro j
      rcases hsign b j₀ with h | h <;> rcases hsign b j with h' | h' <;> simp [v,h,h']
    have horth : ∑ j, u j * v j = 0 := by
      have hc := congrArg (fun M => M a b) hH.mul_conjTranspose
      have hg : (∑ j, H a j * H b j) = 0 := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
          Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
          Matrix.one_apply, smul_eq_mul, hne, ite_false, mul_zero] using hc
      calc
        _ = (H a j₀ * H b j₀) * (∑ j, H a j * H b j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          dsimp [u,v]
          ring
        _ = 0 := by rw [hg, mul_zero]
    let s := Finset.univ.image J
    have hs : s.card = d + 1 := by
      dsimp [s]
      rw [Finset.card_image_of_injective _ J.injective]
      simp
    obtain ⟨j, hj, hdiffer⟩ := orthogonal_sign_rows_separated_on_majority u v hu hv horth s
      (by simp only [Fintype.card_fin, hs]; exact hmajor)
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    apply hdiffer
    refine Fin.cases ?_ (fun i => ?_) i
    · change H a j₀ * H a j₀ = H b j₀ * H b j₀
      nlinarith [hsquare a, hsquare b]
    · change H a j₀ * H a (J i.succ) = H b j₀ * H b (J i.succ)
      rw [← hvalue a i, ← hvalue b i]
      exact congrArg (fun f => (f i : ℝ)) hab
  simpa only [Fintype.card_fin, N] using
    cube_law_of_uniform_sign_frame x hinj hxsign
      (by rw [Fintype.card_fin]; dsimp [N,roundedDimension]; omega)
      hmean hpair

end EntropyDesigns
