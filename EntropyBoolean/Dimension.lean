/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyBoolean.Affine
@[expose] public section
namespace EntropyDesigns
noncomputable section

theorem lowDegreeBooleanCode_half_dimension {r d : ℕ} (hd : 2*d<r) :
    2*Module.finrank (ZMod 2) (lowDegreeBooleanCode r d)≤2^r := by
  have hle := lowDegreeBooleanCode_orthogonal_le (r:=r) (d:=d) (e:=d) (by omega)
  have hh := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal (booleanCubeDotForm_nondegenerate r)] at hh
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_finset,Fintype.card_fin] at hh
  have hnat : ∀ a b : ℕ, a≤b-a → 2*a≤b := by omega
  exact hnat _ _ hh

theorem lowDegreeBooleanCode_degree_of_independent_family {r d M : ℕ}
    (hr : 0<r) (hM : 2^(r-1)<M)
    (f : Fin M → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r d) (hLI : LinearIndependent (ZMod 2) f) :
    r≤2*d := by
  by_contra! hd
  have hh := lowDegreeBooleanCode_half_dimension (r:=r) (d:=d) hd
  let fv : Fin M → lowDegreeBooleanCode r d := fun i => ⟨f i,hf i⟩
  have hi : LinearIndependent (ZMod 2) fv := by
    apply LinearIndependent.of_comp (lowDegreeBooleanCode r d).subtype
    exact hLI
  have hc := hi.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hc
  have he : 2^r=2*2^(r-1) := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hr]
    rw [Nat.pow_succ]
    simp [Nat.pred_eq_sub_one,Nat.mul_comm]
  rw [he] at hh
  generalize hv : 2^(r-1)=v at *
  omega

end
end EntropyDesigns
