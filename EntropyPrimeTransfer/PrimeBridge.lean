/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.PaleySecond
public import EntropyGapTransfer.BufferedOrder
@[expose] public section
namespace EntropyDesigns.PrimeTransfer
open Filter Set
open scoped Topology
noncomputable section

/-- Recover an actual integral sign matrix from a real Hadamard matrix. -/
theorem integer_of_real_hadamard {n : ℕ} (hn : 0<n)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Matrix.IsHadamard H) :
    ∃ K : Matrix (Fin n) (Fin n) ℤ, Matrix.IsHadamard K := by
  classical
  let K : Matrix (Fin n) (Fin n) ℤ := fun i j => if H i j=1 then 1 else -1
  have he (i j : Fin n) : (K i j : ℝ)=H i j := by
    rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i j) with h|h
    · norm_num [K,h]
    · norm_num [K,h]
  refine ⟨K,Matrix.IsHadamard.of_mul_conjTranspose ?_ ?_ ?_⟩
  · intro i j
    apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
    dsimp [K]
    split_ifs <;> simp
  · ext i j
    apply Int.cast_injective (α:=ℝ)
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hH.mul_conjTranspose
    simpa [Matrix.mul_apply,Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,he] using hh
  · apply isRegular_iff_ne_zero.mpr
    simp only [Fintype.card_fin]
    exact_mod_cast (Nat.ne_of_gt hn)

/-- Paley supplies an integral known order from any odd prime. -/
theorem prime_known_order {p : ℕ} (hp : p.Prime) (hodd : p≠2) :
    GapTransfer.knownHadamardOrder (2*(p+1)) := by
  obtain ⟨H,hH⟩ := odd_prime_twice_successor_hadamard hp hodd
  exact integer_of_real_hadamard (by omega) H hH

/-- A single ordinary prime interval gives a preceding known Hadamard order.
No residue-class restriction and no unproved distribution theorem is used. -/
theorem prime_interval_known_order (G : ℝ → ℝ) (hmono : MonotoneOn G (Ici 0))
    (x : ℝ) (hx : 6<x) (hs : 2<x/2-1-G (x/2-1))
    (hp : ∃ p : ℕ,p.Prime ∧ x/2-1-G (x/2-1)≤(p:ℝ) ∧ (p:ℝ)≤x/2-1) :
    ∃ k : ℕ,GapTransfer.knownHadamardOrder k ∧ x-2*G (x/2)≤(k:ℝ) ∧ (k:ℝ)≤x := by
  obtain ⟨p,hprime,hlo,hhi⟩ := hp
  have hp2 : p≠2 := by intro h;subst p;norm_num at hlo;linarith
  have hg : G (x/2-1)≤G (x/2) := hmono (by change 0≤_;linarith) (by change 0≤_;linarith) (by linarith)
  refine ⟨2*(p+1),prime_known_order hprime hp2,?_,?_⟩ <;> push_cast <;> linarith

end
end EntropyDesigns.PrimeTransfer
