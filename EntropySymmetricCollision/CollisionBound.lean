/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySymmetricCollision.CollisionSlices
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EntropyDesigns.SymmetricEntropy
noncomputable section
open scoped BigOperators

def weightRegion (d : ℕ) (P : ℕ → Prop) : Finset (Fin d → Bool) := by
  classical
  exact Finset.univ.filter fun x => P (hammingWeight x)

theorem mem_weightRegion {d : ℕ} (P : ℕ → Prop) (x : Fin d → Bool) :
    x∈weightRegion d P ↔ P (hammingWeight x) := by
  classical
  simp [weightRegion]

theorem weightRegion_orbit_closed {d : ℕ} (P : ℕ → Prop)
    (x : Fin d → Bool) (hx : x∈weightRegion d P) :
    hammingSlice d (hammingWeight x)⊆weightRegion d P := by
  classical
  intro y hy
  have hxy : hammingWeight y=hammingWeight x := (Finset.mem_filter.mp hy).2
  have hxP : P (hammingWeight x) := (mem_weightRegion P x).mp hx
  exact (mem_weightRegion P y).mpr (hxy.symm ▸ hxP)

theorem region_mass_range {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1) (T : Finset (Fin d → Bool)) :
    0≤∑ x∈T,w x ∧ (∑ x∈T,w x)≤1 := by
  classical
  constructor
  · exact Finset.sum_nonneg fun x _ => hw x
  · rw [←hmass]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hw x)

theorem symmetric_collision_upper {d : ℕ} (hd : 7≤d)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hsym : CoordinatePermutationInvariant w)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    collision w≤1/(d:ℝ)^2+(d:ℝ)/((d:ℝ)-2)^4+2/((d:ℝ)*((d:ℝ)-1)) := by
  classical
  let E := weightRegion d (fun k => k=0 ∨ k=d)
  let N := weightRegion d (fun k => k=1 ∨ k=d-1)
  let M := weightRegion d (fun k => 2≤k ∧ k≤d-2)
  have hdR : (7:ℝ)≤d := by exact_mod_cast hd
  have hd0 : (0:ℝ)<d := by linarith
  have hd2 : (0:ℝ)<(d:ℝ)-2 := by linarith
  have hmE := (region_mass_range w hw hmass E).1
  have hmN := (region_mass_range w hw hmass N).1
  have hmM := region_mass_range w hw hmass M
  have heMass : (∑ x∈E,w x)≤1/(d:ℝ) := by
    convert SymmetricCollision.endpoint_mass_bound (show 0<d by omega) w hw hmass hmean hpair using 1 <;>
      congr 1 <;> ext x <;> simp [E,weightRegion]
  have hnMass : (∑ x∈N,w x)≤(d:ℝ)/((d:ℝ)-2)^2 := by
    convert SymmetricCollision.neighboring_mass_bound (show 2<d by omega) w hw hmass hmean hpair using 1 <;>
      congr 1 <;> ext x <;> simp [N,weightRegion]
  have he : (∑ x∈E,(w x)^2)≤1/(d:ℝ)^2 := by
    have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s:=E) (f:=w) (fun x _ => hw x)
    have hb : (∑ x∈E,w x)^2≤(1/(d:ℝ))^2 := by nlinarith
    have hid : (1/(d:ℝ))^2=1/(d:ℝ)^2 := by field_simp
    exact hh.trans (hid ▸ hb)
  have hn : (∑ x∈N,(w x)^2)≤(d:ℝ)/((d:ℝ)-2)^4 := by
    have hh := symmetric_region_collision_cap w hw hsym N (d:ℝ)
      (fun x hx => weightRegion_orbit_closed _ x hx) (by
        intro x hx
        rcases (mem_weightRegion _ x).mp hx with h|h
        · simp [h]
        · simp [h,Nat.choose_symm (show 1≤d by omega)])
    have hb : (∑ x∈N,w x)^2≤((d:ℝ)/((d:ℝ)-2)^2)^2 := by
      have hq : 0≤(d:ℝ)/((d:ℝ)-2)^2 := by positivity
      nlinarith
    have hc : (∑ x∈N,(w x)^2)≤((d:ℝ)/((d:ℝ)-2)^2)^2/(d:ℝ) :=
      (le_div_iff₀ hd0).mpr (by nlinarith)
    have hid : ((d:ℝ)/((d:ℝ)-2)^2)^2/(d:ℝ)=(d:ℝ)/((d:ℝ)-2)^4 := by
      field_simp
      <;> ring
    exact hid ▸ hc
  have hC : (0:ℝ)<Nat.choose d 2 := by exact_mod_cast Nat.choose_pos (show 2≤d by omega)
  have hm : (∑ x∈M,(w x)^2)≤2/((d:ℝ)*((d:ℝ)-1)) := by
    have hh := symmetric_region_collision_cap w hw hsym M (Nat.choose d 2:ℝ)
      (fun x hx => weightRegion_orbit_closed _ x hx) (by
        intro x hx
        obtain ⟨hlo,hhi⟩ := (mem_weightRegion _ x).mp hx
        exact_mod_cast choose_two_le_middle hlo hhi)
    have hb : (∑ x∈M,w x)^2≤1 := by nlinarith [hmM.1,hmM.2]
    have hc : (∑ x∈M,(w x)^2)≤1/(Nat.choose d 2:ℝ) := (le_div_iff₀ hC).mpr (by nlinarith)
    have hid : (1:ℝ)/(Nat.choose d 2:ℝ)=2/((d:ℝ)*((d:ℝ)-1)) := by
      have hh := congrArg (fun n : ℕ => (n:ℝ)) (Nat.choose_succ_right_eq d 1)
      have hr : (Nat.choose d 2:ℝ)*2=(d:ℝ)*((d:ℝ)-1) := by
        simpa [Nat.cast_sub (show 1≤d by omega)] using hh
      rw [←hr]
      field_simp
      <;> ring
    exact hid ▸ hc
  have hsplit : collision w=(∑ x∈E,(w x)^2)+(∑ x∈N,(w x)^2)+(∑ x∈M,(w x)^2) := by
    unfold collision
    simp only [E,N,M,weightRegion,Finset.sum_filter]
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    have hk : hammingWeight x≤d := by
      unfold hammingWeight
      simpa using Finset.card_le_card (Finset.filter_subset (fun i : Fin d => x i=true) Finset.univ)
    by_cases he : hammingWeight x=0 ∨ hammingWeight x=d
    · have hn : ¬(hammingWeight x=1 ∨ hammingWeight x=d-1) := by rcases he with h|h <;> omega
      have hm : ¬(2≤hammingWeight x ∧ hammingWeight x≤d-2) := by rcases he with h|h <;> omega
      simp [he,hn,hm]
    · by_cases hn : hammingWeight x=1 ∨ hammingWeight x=d-1
      · have hm : ¬(2≤hammingWeight x ∧ hammingWeight x≤d-2) := by rcases hn with h|h <;> omega
        simp [he,hn,hm]
      · have hm : 2≤hammingWeight x ∧ hammingWeight x≤d-2 := by omega
        simp [he,hn,hm]
  rw [hsplit]
  linarith

end
end EntropyDesigns.SymmetricEntropy
