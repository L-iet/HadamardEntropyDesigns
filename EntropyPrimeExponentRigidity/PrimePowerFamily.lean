/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPrimeExponentRigidity.PrimeDivisor
public import EntropyDesigns.Paley
@[expose] public section
namespace EntropyDesigns.PrimeExponentRigidity
noncomputable section

def primePowerOrder (k : ℕ) : ℕ := 3^k+1

def primePowerOddParameter (k : ℕ) : ℕ := (3^k+1)/4

theorem paley_prime_exponent_order (k : ℕ) (hko : Odd k) :
    ∃ A : Matrix (Fin (primePowerOrder k)) (Fin (primePowerOrder k)) ℤ,A.IsHadamard := by
  classical
  obtain ⟨t,ht⟩ := hko
  have hk0 : k≠0 := by omega
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let F := GaloisField 3 k
  letI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F=3^k := by
    simpa only [Nat.card_eq_fintype_card] using GaloisField.card (p := 3) (n := k) hk0
  have hres : Fintype.card F%4=3 := by
    rw [hc,ht,pow_add,pow_mul]
    norm_num [Nat.mul_mod,Nat.pow_mod]
  let e : Option F ≃ Fin (primePowerOrder k) :=
    (Fintype.equivFin _).trans (finCongr (by simp only [Fintype.card_option,hc,primePowerOrder]))
  exact ⟨_,(paley_integer_hadamard (F:=F) hres).reindex e e⟩

theorem prime_power_parameter_properties (k : ℕ) (hk : k.Prime) (hko : Odd k) :
    4*primePowerOddParameter k=primePowerOrder k ∧ Odd (primePowerOddParameter k) ∧
    1<primePowerOddParameter k ∧ (primePowerOrder k)%8=4 := by
  obtain ⟨t,ht⟩ := hko
  have hres : (3^k+1)%8=4 := by rw [ht];exact paley_three_power_order_residue t
  have hk2 : k≠2 := by intro he;rw [he] at ht;omega
  have hk3 : 3≤k := by have hh := hk.two_le;omega
  have hp : 3^3≤3^k := Nat.pow_le_pow_right (by decide) hk3
  norm_num at hp
  have hdiv : 4*((3^k+1)/4)=3^k+1 := by omega
  refine ⟨hdiv,?_,?_,hres⟩
  · apply Nat.odd_iff.mpr
    change ((3^k+1)/4)%2=1
    omega
  · change 1<(3^k+1)/4
    omega

theorem prime_power_parameter_roughness (k : ℕ) (hk : k.Prime) (hko : Odd k) :
    2*k+1≤(primePowerOddParameter k).minFac := by
  obtain ⟨hfour,hmOdd,hm,hres⟩ := prime_power_parameter_properties k hk hko
  let m := primePowerOddParameter k
  have hp : m.minFac.Prime := Nat.minFac_prime (by change primePowerOddParameter k≠1;omega)
  have hd : m.minFac∣m := Nat.minFac_dvd m
  have hpo : Odd m.minFac := hmOdd.of_dvd_nat hd
  have hp2 : m.minFac≠2 := by
    intro he
    rw [he] at hpo
    obtain ⟨z,hz⟩ := hpo
    omega
  have hdn : m.minFac∣3^k+1 := by
    have hh : m.minFac∣4*m := dvd_mul_of_dvd_right hd 4
    simpa only [m,hfour,primePowerOrder] using hh
  have horder := prime_divisor_of_three_prime_power_successor k m.minFac hk hko hp hp2 hdn
  have hl3 : 3≤m.minFac := by have hh := hp.two_le;omega
  have hle := Nat.le_of_dvd (by omega : 0<m.minFac-1) horder
  change 2*k+1≤m.minFac
  omega

end
end EntropyDesigns.PrimeExponentRigidity
