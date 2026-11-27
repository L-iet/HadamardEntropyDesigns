/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentratedFamily.FiniteFieldSupports
public import Mathlib.Algebra.Divisibility.Basic
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.ConcentratedFamily
noncomputable section
open SupportFace

theorem family_parameters {k s : ℕ} (hk : 2≤k) (hsize : 2*(k-1)<2^s) :
    2≤s ∧ s≠0 ∧ k≤2^s := by
  have hkh : k≤2^s := by omega
  have hs : 2≤s := by
    by_contra h
    have h01 : s=0 ∨ s=1 := by omega
    rcases h01 with h0|h1
    · subst s;norm_num at hsize;omega
    · subst s;norm_num at hsize;omega
  exact ⟨hs,by omega,hkh⟩

theorem concentrated_slopes_exist {k s : ℕ} (hk : 2≤k) (hsize : 2*(k-1)<2^s) :
    ∃ t : Fin k → GaloisField 2 s,Function.Injective t := by
  classical
  obtain ⟨_,hs,hkh⟩ := family_parameters hk hsize
  let F := GaloisField 2 s
  letI : Fintype F := Fintype.ofFinite F
  have hFcard : Fintype.card F=2^s := by
    simpa only [Nat.card_eq_fintype_card] using (GaloisField.card (p:=2) (n:=s) hs)
  let E : F ≃ Fin (2^s) := Fintype.equivFinOfCardEq hFcard
  refine ⟨fun j => E.symm ⟨j.val,lt_of_lt_of_le j.isLt hkh⟩,?_⟩
  intro a b hab
  apply Fin.ext
  have hv := congrArg (fun x : F => (E x).val) hab
  simpa only [Equiv.apply_symm_apply] using hv

theorem fieldOffsetImage_divisible {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) (hs : s≠0) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    k∣(fieldOffsetImage hs i0 t).card := by
  rw [fieldOffsetImage_card hk hs i0 t ht]
  have hkh : k≤2^s := (family_parameters hk hsize).2.2
  have hpowle : (2:ℕ)^r≤2^s := by simpa only [←hkpow] using hkh
  have hrs : r≤s := (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hpowle
  simpa only [←hkpow] using (pow_dvd_pow (2:ℕ) hrs)

theorem canonical_family_parameters {r : ℕ} (hr : 1≤r) :
    2≤2^r ∧ 2*((2^r)-1)<2^(2*r) ∧ 2^(2*r)=(2^r)^2 := by
  have hk : 2≤2^r := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mpr hr
    simpa using h
  have heq : (2:ℕ)^(2*r)=(2^r)^2 := by rw [Nat.mul_comm,pow_mul]
  refine ⟨hk,?_,heq⟩
  rw [heq]
  have hsub : (2^r)-1+1=2^r := Nat.sub_add_cancel (by omega)
  calc
    2*((2^r)-1)<((2^r)-1+1)^2 := by nlinarith [Nat.zero_le (((2^r)-1)^2)]
    _=(2^r)^2 := by rw [hsub]

end
end EntropyDesigns.ConcentratedFamily
