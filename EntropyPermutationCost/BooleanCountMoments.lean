/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.CubeIsolation
@[expose] public section
namespace EntropyDesigns.PermutationCost
open scoped BigOperators

 theorem boolean_sign_sum_from_true_count {α : Type*} [Fintype α]
    (f : α → Bool) (hc : 2*(Finset.univ.filter (fun r => f r=true)).card=Fintype.card α) :
    (∑ r,bitSign (f r))=0 := by
  classical
  have hp (r : α) : bitSign (f r)=1-2*(if f r=true then (1:ℤ) else 0) := by
    cases h : f r <;> norm_num [h,bitSign]
  have hs : (∑ r,bitSign (f r))=(Fintype.card α:ℤ)-
      2*((Finset.univ.filter (fun r => f r=true)).card:ℤ) := by
    simp_rw [hp]
    simp [Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_ite,mul_comm]
  have hh : (2:ℤ)*((Finset.univ.filter (fun r => f r=true)).card:ℤ)=Fintype.card α := by exact_mod_cast hc
  omega

 theorem boolean_pair_sign_sum_from_counts {α : Type*} [Fintype α]
    (f g : α → Bool)
    (hf : 2*(Finset.univ.filter (fun r => f r=true)).card=Fintype.card α)
    (hg : 2*(Finset.univ.filter (fun r => g r=true)).card=Fintype.card α)
    (hp : 4*(Finset.univ.filter (fun r => f r=true ∧ g r=true)).card=Fintype.card α) :
    (∑ r,bitSign (f r)*bitSign (g r))=0 := by
  classical
  have ht (r : α) : bitSign (f r)*bitSign (g r)=
      1-2*(if f r=true then (1:ℤ) else 0)-2*(if g r=true then (1:ℤ) else 0)+
        4*(if f r=true ∧ g r=true then (1:ℤ) else 0) := by
    cases h1 : f r <;> cases h2 : g r <;> norm_num [h1,h2,bitSign]
  have hs : (∑ r,bitSign (f r)*bitSign (g r))=(Fintype.card α:ℤ)-
      2*((Finset.univ.filter (fun r => f r=true)).card:ℤ)-
      2*((Finset.univ.filter (fun r => g r=true)).card:ℤ)+
      4*((Finset.univ.filter (fun r => f r=true ∧ g r=true)).card:ℤ) := by
    simp_rw [ht]
    simp [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_ite,mul_comm]
  have hf' : (2:ℤ)*((Finset.univ.filter (fun r => f r=true)).card:ℤ)=Fintype.card α := by exact_mod_cast hf
  have hg' : (2:ℤ)*((Finset.univ.filter (fun r => g r=true)).card:ℤ)=Fintype.card α := by exact_mod_cast hg
  have hp' : (4:ℤ)*((Finset.univ.filter (fun r => f r=true ∧ g r=true)).card:ℤ)=Fintype.card α := by exact_mod_cast hp
  omega

end EntropyDesigns.PermutationCost
