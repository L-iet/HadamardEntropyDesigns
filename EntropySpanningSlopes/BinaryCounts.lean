/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySpanningSlopes.FunctionalEscape
public import EntropySupportFace.BinaryCharacters
@[expose] public section
namespace EntropyDesigns.SpanningSlopes
noncomputable section
open SupportFace
open scoped BigOperators

theorem binary_functional_one_count {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (f : V →ₗ[ZMod 2] ZMod 2) (hf : f≠0) :
    (Finset.univ.filter (fun x : V => f x=1)).card=Fintype.card V/2 := by
  classical
  have h := binary_functional_sum_zero f hf
  have hs (x : V) : binarySign (f x)=1-2*(if f x=1 then (1:ℝ) else 0) := by
    rcases binaryField_cases (f x) with hx|hx <;> norm_num [binarySign,hx]
  have hc : (∑ x : V,if f x=1 then (1:ℝ) else 0)=
      ((Finset.univ.filter (fun x : V => f x=1)).card:ℝ) := by
    rw [←Finset.sum_filter]
    simp
  simp_rw [hs] at h
  rw [Finset.sum_sub_distrib] at h
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,←Finset.mul_sum,hc] at h
  have hn : 2*(Finset.univ.filter (fun x : V => f x=1)).card=Fintype.card V := by
    exact_mod_cast (show (2:ℝ)*((Finset.univ.filter (fun x : V => f x=1)).card:ℝ)=
      (Fintype.card V:ℝ) by linarith)
  omega

theorem scaled_binary_one_count {K : Type*} [Field K] [Algebra (ZMod 2) K]
    [Fintype K] (f : K →ₗ[ZMod 2] ZMod 2) (hf : f≠0) (b : K) (hb : b≠0) :
    (Finset.univ.filter (fun t : K => f (t*b)=1)).card=Fintype.card K/2 := by
  have hg : f.comp (rightMulLinear b)≠0 := by
    intro hg
    apply hf
    apply LinearMap.ext
    intro z
    have h := LinearMap.congr_fun hg (z*b⁻¹)
    simpa [rightMulLinear,mul_assoc,hb] using h
  exact binary_functional_one_count (f.comp (rightMulLinear b)) hg

theorem omitted_spanning_count_window {K : Type*} [Field K] [Algebra (ZMod 2) K]
    [Fintype K] [DecidableEq K] (R : Finset K) (hspan : Submodule.span (ZMod 2) (R:Set K)=⊤)
    (hsmall : R.card<Fintype.card K/2)
    (f : K →ₗ[ZMod 2] ZMod 2) (hf : f≠0) (b : K) (hb : b≠0) :
    0<((Finset.univ\R).filter (fun t : K => f (t*b)=1)).card ∧
      ((Finset.univ\R).filter (fun t : K => f (t*b)=1)).card<Fintype.card K/2 := by
  classical
  let Q := Finset.univ.filter (fun t : K => f (t*b)=1)
  have hQ : Q.card=Fintype.card K/2 := scaled_binary_one_count f hf b hb
  have hleft : Q.filter (fun t => t∈R)=R.filter (fun t => f (t*b)=1) := by
    ext t
    simp [Q,and_comm]
  have hright : Q.filter (fun t => t∉R)=(Finset.univ\R).filter (fun t => f (t*b)=1) := by
    ext t
    simp [Q,and_comm]
  have hsum := Finset.card_filter_add_card_filter_not (s:=Q) (fun t => t∈R)
  rw [hleft,hright,hQ] at hsum
  obtain ⟨t,ht,hft⟩ := spanning_set_escapes_scaled_kernel (R:Set K) hspan f hf b hb
  have hval : f (t*b)=1 := by
    rcases binaryField_cases (f (t*b)) with h0|h1
    · exact False.elim (hft h0)
    · exact h1
  have hpos : 0<(R.filter (fun t => f (t*b)=1)).card :=
    Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,hval⟩⟩
  have hle : (R.filter (fun t => f (t*b)=1)).card≤R.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

end
end EntropyDesigns.SpanningSlopes
