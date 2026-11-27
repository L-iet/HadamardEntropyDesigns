/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.HammingWeight
@[expose] public section
namespace EntropyDesigns.SymmetricCollision
noncomputable section
open scoped BigOperators

def weightSpin {d : ℕ} (x : Fin d → Bool) : ℝ := 2*(hammingWeight x:ℝ)-d

theorem weightSpin_second_moment {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hmass : ∑ x,w x=1)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    (∑ x,w x*(weightSpin x)^2)=(d:ℝ) := by
  obtain ⟨h1,h2⟩ := hamming_moments w hmass hmean hpair
  have he (x : Fin d → Bool) : w x*(weightSpin x)^2=
      4*(w x*(hammingWeight x:ℝ)^2)-4*(d:ℝ)*(w x*(hammingWeight x:ℝ))+(d:ℝ)^2*w x := by
    unfold weightSpin
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,
    ←Finset.mul_sum,h1,h2,hmass]
  ring

theorem support_mass_second_moment {α : Type*} [Fintype α]
    (w f : α → ℝ) (hw : ∀ x,0≤w x) (T : Finset α) (b : ℝ)
    (hbound : ∀ x∈T,b≤(f x)^2) :
    b*(∑ x∈T,w x)≤∑ x,w x*(f x)^2 := by
  classical
  calc
    _ = ∑ x∈T,w x*b := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
    _ ≤ ∑ x∈T,w x*(f x)^2 := Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (hbound x hx) (hw x))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => mul_nonneg (hw x) (sq_nonneg (f x)))

theorem endpoint_mass_bound {d : ℕ} (hd : 0<d)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    (∑ x∈Finset.univ.filter (fun x => hammingWeight x=0 ∨ hammingWeight x=d),w x)≤1/(d:ℝ) := by
  classical
  let T := Finset.univ.filter fun x : Fin d → Bool => hammingWeight x=0 ∨ hammingWeight x=d
  have hb : ∀ x∈T,(d:ℝ)^2≤(weightSpin x)^2 := by
    intro x hx
    rcases (Finset.mem_filter.mp hx).2 with h|h
    · simp [weightSpin,h]
    · simp [weightSpin,h]; nlinarith
  have hh := support_mass_second_moment w weightSpin hw T ((d:ℝ)^2) hb
  rw [weightSpin_second_moment w hmass hmean hpair] at hh
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  change (∑ x∈T,w x)≤1/(d:ℝ)
  apply (le_div_iff₀ hdR).mpr
  nlinarith [mul_pos hdR hdR]


theorem neighboring_mass_bound {d : ℕ} (hd : 2<d)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    (∑ x∈Finset.univ.filter (fun x => hammingWeight x=1 ∨ hammingWeight x=d-1),w x)≤
      (d:ℝ)/((d:ℝ)-2)^2 := by
  classical
  let T := Finset.univ.filter fun x : Fin d → Bool => hammingWeight x=1 ∨ hammingWeight x=d-1
  have hdR : (2:ℝ)<d := by exact_mod_cast hd
  have hb : ∀ x∈T,((d:ℝ)-2)^2≤(weightSpin x)^2 := by
    intro x hx
    rcases (Finset.mem_filter.mp hx).2 with h|h
    · simp only [weightSpin,h,Nat.cast_one]
      nlinarith [sq_nonneg ((d:ℝ)-2)]
    · simp only [weightSpin,h,Nat.cast_sub (show 1≤d by omega),Nat.cast_one]
      nlinarith [sq_nonneg ((d:ℝ)-2)]
  have hh := support_mass_second_moment w weightSpin hw T (((d:ℝ)-2)^2) hb
  rw [weightSpin_second_moment w hmass hmean hpair] at hh
  change (∑ x∈T,w x)≤(d:ℝ)/((d:ℝ)-2)^2
  apply (le_div_iff₀ (sq_pos_of_pos (by linarith : (0:ℝ)<(d:ℝ)-2))).mpr
  nlinarith

end
end EntropyDesigns.SymmetricCollision
