/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.UniformSource
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

theorem source_uniform_law {k s : ℕ} (hk : 2≤k) (hkh : k≤2^s)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k) :
    ∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ sourceSupported e i0 q ∧
      collision q=1/((2:ℝ)^s)^k ∧
      (∀ x : BlockSeeds k s,q (sourceCode e i0 x)=1/((2:ℝ)^s)^k) ∧
      (observedSupport e i0).card=(2^s)^k := by
  classical
  have hs : s≠0 := by intro h;subst s;norm_num at hkh;omega
  let F := GaloisField 2 s
  letI : Fintype F := Fintype.ofFinite F
  have hFcard : Fintype.card F=2^s := by
    simpa only [Nat.card_eq_fintype_card] using (GaloisField.card (p:=2) (n:=s) hs)
  let ef : F ≃ Fin (2^s) := Fintype.equivFinOfCardEq hFcard
  let t : Fin k ↪ F :=
    { toFun := fun j => ef.symm ⟨j.val,lt_of_lt_of_le j.isLt hkh⟩
      inj' := by
        intro a b h
        apply Fin.ext
        have hv := congrArg (fun x : F => (ef x).val) h
        simpa only [Equiv.apply_symm_apply] using hv }
  exact uniform_source_of_slopes hs e he i0 t t.injective

theorem source_all_mixtures_distance_lower {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (hsize : 2*(k-1)<2^s) (p q : SourceOutcome k s i0 → ℝ)
    (hp : ∑ x,p x=1) (hsupport : sourceSupported e i0 p)
    (hq : q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s))) :
    1-1/(k:ℝ)≤totalVariation p q := by
  classical
  have hk : 0<k := by have h := i0.isLt;omega
  have hh : 0<2^s := pow_pos (by decide) s
  have hs : ∀ y,y∉observedSupport e i0 → p y=0 := by
    intro y hy
    apply hsupport y
    intro hex
    obtain ⟨x,hx⟩ := hex
    exact hy (Finset.mem_image.mpr ⟨x,Finset.mem_univ x,hx⟩)
  have h := SupportWitness.support_witness_all_mixtures observedOrthogonal
    (observedSupport e i0) (Nat.mul_pos hk hh) p hp hs q hq
  rw [observed_orthogonality_number e i0 hsize] at h
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have hh0 : (2:ℝ)^s≠0 := pow_ne_zero s (by norm_num)
  have hratio : ((2^s:ℕ):ℝ)/((k*2^s:ℕ):ℝ)=1/(k:ℝ) := by
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  rw [hratio] at h
  exact h

end
end EntropyDesigns.SupportFace
