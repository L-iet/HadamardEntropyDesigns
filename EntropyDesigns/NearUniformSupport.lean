module

public import EntropyDesigns.DefectDecomposition

/-! # Finite support extraction from a near-uniform weighted law -/

@[expose] public section
namespace EntropyDesigns

/-- A finite weighted Markov bound, stated for an arbitrary proposed good set. -/
theorem mass_outside_good_set {α : Type*} [Fintype α] [DecidableEq α]
    (w f : α → ℝ) (G : Finset α) (η : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hf : ∀ a, 0 ≤ f a)
    (hbad : ∀ a, a ∉ G → η ≤ f a) :
    η * (∑ a ∈ Gᶜ, w a) ≤ ∑ a, w a * f a := by
  calc
    η * (∑ a ∈ Gᶜ, w a) = ∑ a ∈ Gᶜ, w a * η := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ∑ a ∈ Gᶜ, w a * f a := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hbad a (Finset.mem_compl.mp ha)) (hw a)
    _ ≤ ∑ a, w a * f a := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun a _ _ => mul_nonneg (hw a) (hf a))

/-- A sufficiently narrow weight interval and small omitted mass determine
the exact number of retained atoms. -/
theorem support_card_of_mass_window {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (G : Finset α) (N : ℕ) (_hN : 1 ≤ N)
    (lo hi β : ℝ) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hweights : ∀ a ∈ G, lo ≤ w a ∧ w a ≤ hi)
    (hbad : (∑ a ∈ Gᶜ, w a) < β)
    (hlarge : 1 < ((N : ℝ) + 1) * lo)
    (hsmall : ((N : ℝ) - 1) * hi < 1 - β) :
    G.card = N := by
  have hpartition : (∑ a ∈ G, w a) + ∑ a ∈ Gᶜ, w a = 1 := by
    rw [Finset.sum_add_sum_compl, hmass]
  have hgood_nonneg : 0 ≤ ∑ a ∈ Gᶜ, w a :=
    Finset.sum_nonneg (fun a _ => hw a)
  have hlower : (G.card : ℝ) * lo ≤ ∑ a ∈ G, w a := by
    calc
      _ = ∑ _a ∈ G, lo := by simp
      _ ≤ _ := Finset.sum_le_sum (fun a ha => (hweights a ha).1)
  have hupper : (∑ a ∈ G, w a) ≤ (G.card : ℝ) * hi := by
    calc
      _ ≤ ∑ _a ∈ G, hi := Finset.sum_le_sum (fun a ha => (hweights a ha).2)
      _ = _ := by simp
  have hle : G.card ≤ N := by
    by_contra h
    have hc : N + 1 ≤ G.card := by omega
    have hcr : (N : ℝ) + 1 ≤ G.card := by exact_mod_cast hc
    have hm := mul_le_mul_of_nonneg_right hcr hlo
    linarith
  have hge : N ≤ G.card := by
    by_contra h
    have hc : G.card + 1 ≤ N := by omega
    have hcr : (G.card : ℝ) ≤ (N : ℝ) - 1 := by
      have : (G.card : ℝ) + 1 ≤ N := by exact_mod_cast hc
      linarith
    have hm := mul_le_mul_of_nonneg_right hcr hhi
    linarith
  exact Nat.le_antisymm hle hge

/-- The narrow good-weight window contains exactly N atoms. -/
theorem near_uniform_support_card {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (N : ℕ) (hN : 8 ≤ N)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (herror : (∑ a, w a * |(N : ℝ) * w a - 1|) < 1 / (8 * (N : ℝ) ^ 2)) :
    (Finset.univ.filter (fun a => |(N : ℝ) * w a - 1| ≤
      1 / (4 * (N : ℝ)))).card = N := by
  classical
  let R : ℝ := N
  let η : ℝ := 1 / (4 * R)
  let G := Finset.univ.filter (fun a => |R * w a - 1| ≤ η)
  have hR8 : (8 : ℝ) ≤ R := by dsimp [R]; exact_mod_cast hN
  have hR : 0 < R := by linarith
  have hη : 0 < η := div_pos zero_lt_one (by positivity)
  have hηle : η ≤ 1 / 4 := by
    dsimp [η]
    apply (div_le_iff₀ (by positivity : 0 < 4 * R)).2
    nlinarith
  have hηR : η * R = 1 / 4 := by dsimp [η]; field_simp
  have hmark := mass_outside_good_set w (fun a => |R * w a - 1|) G η hw
    (fun _ => abs_nonneg _) (by
      intro a ha
      have : ¬|R * w a - 1| ≤ η := by simpa [G] using ha
      exact (lt_of_not_ge this).le)
  have hscale : η * (1 / (2 * R)) = 1 / (8 * R ^ 2) := by
    dsimp [η]
    field_simp
    ring
  have hbad : (∑ a ∈ Gᶜ, w a) < 1 / (2 * R) := by
    apply (mul_lt_mul_iff_right₀ hη).mp
    rw [hscale]
    exact hmark.trans_lt herror
  have hweights : ∀ a ∈ G, (1 - η) / R ≤ w a ∧ w a ≤ (1 + η) / R := by
    intro a ha
    have hh : |R * w a - 1| ≤ η := (Finset.mem_filter.mp ha).2
    have hab := abs_le.mp hh
    constructor
    · apply (div_le_iff₀ hR).2
      nlinarith
    · apply (le_div_iff₀ hR).2
      nlinarith
  have hlarge : 1 < (R + 1) * ((1 - η) / R) := by
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ hR).2
    nlinarith [hηR]
  have hsmall : (R - 1) * ((1 + η) / R) < 1 - 1 / (2 * R) := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hR).2
    have hcancel : (1 / (2 * R)) * R = 1 / 2 := by field_simp
    nlinarith [hηR, hcancel]
  exact support_card_of_mass_window w G N (by omega) ((1 - η) / R) ((1 + η) / R)
    (1 / (2 * R)) (div_nonneg (by linarith) hR.le)
    (div_nonneg (by linarith) hR.le) hw hmass hweights hbad hlarge hsmall

/-- The explicit deficit threshold is small enough for finite support extraction. -/
theorem extraction_numeric_window {N D δ : ℝ} (hN : 8 ≤ N)
    (hD : N ^ 2 / 2 ≤ D) (_hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (1024 * N ^ 4)) :
    N * (Real.sqrt (2 * δ / D) + δ) < 1 / (8 * N ^ 2) := by
  have hNpos : 0 < N := by linarith
  have hDpos : 0 < D := by nlinarith [sq_pos_of_pos hNpos]
  have hidentity : 2 * (1 / (1024 * N ^ 4)) =
      (1 / (16 * N ^ 3)) ^ 2 * (N ^ 2 / 2) := by
    field_simp
    ring
  have hratio : 2 * δ / D ≤ (1 / (16 * N ^ 3)) ^ 2 := by
    apply (div_le_iff₀ hDpos).2
    calc
      2 * δ ≤ 2 * (1 / (1024 * N ^ 4)) := by linarith
      _ = _ := hidentity
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (sq_nonneg _)
  have hroot : Real.sqrt (2 * δ / D) ≤ 1 / (16 * N ^ 3) :=
    (Real.sqrt_le_iff).2 ⟨by positivity, hratio⟩
  have hupper : N * (Real.sqrt (2 * δ / D) + δ) ≤
      N * (1 / (16 * N ^ 3) + 1 / (1024 * N ^ 4)) :=
    mul_le_mul_of_nonneg_left (add_le_add hroot hsmall) hNpos.le
  apply hupper.trans_lt
  apply (mul_lt_mul_iff_left₀ (by positivity : 0 < 1024 * N ^ 3)).mp
  have hleft : (N * (1 / (16 * N ^ 3) + 1 / (1024 * N ^ 4))) *
      (1024 * N ^ 3) = 1 + 64 * N := by
    field_simp
    ring
  have hright : (1 / (8 * N ^ 2)) * (1024 * N ^ 3) = 128 * N := by
    field_simp
    ring
  rw [hleft, hright]
  linarith

theorem normalized_weight_error_identity {α : Type*} [Fintype α]
    (w : α → ℝ) {N : ℝ} (hN : 0 < N) :
    (∑ a, w a * |N * w a - 1|) = N * (∑ a, w a * |w a - 1 / N|) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hid : N * (w a - 1 / N) = N * w a - 1 := by
    rw [mul_sub, mul_one_div_cancel hN.ne']
  rw [← hid, abs_mul, abs_of_pos hN]
  ring

/-- The explicit deficit threshold already determines exactly N good atoms,
before proving that their uniform weights preserve the moments. -/
theorem small_deficit_good_support_card {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 5 ≤ n) (hres : n % 4 = 1)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0)
    (hsmall : 1 / ((n : ℝ) + 3) - collision w ≤ 1 / (1024 * ((n : ℝ) + 3) ^ 4)) :
    (Finset.univ.filter (fun a => |((n : ℝ) + 3) * w a - 1| ≤
      1 / (4 * ((n : ℝ) + 3)))).card = n + 3 := by
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (0 : ℝ) < (n : ℝ) + 3 := by linarith
  have hdev := residue_frame_weight_deviation (by omega) hres A w hsign hw hmass hiso
  have hnum := extraction_numeric_window (by linarith : (8 : ℝ) ≤ (n : ℝ) + 3)
    (by nlinarith : ((n : ℝ) + 3) ^ 2 / 2 ≤ (n : ℝ) ^ 2 + 2 * n - 3)
    (residue_frame_deficit_nonneg (by omega) hres A w hsign hw hmass hiso) hsmall
  have herr : (∑ a, w a * |((n : ℝ) + 3) * w a - 1|) <
      1 / (8 * ((n : ℝ) + 3) ^ 2) := by
    rw [normalized_weight_error_identity w hN]
    exact (mul_le_mul_of_nonneg_left hdev hN.le).trans_lt hnum
  have hc := near_uniform_support_card w (n + 3) (by omega) hw hmass
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using herr)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hc

noncomputable def uniformOn {α : Type*} [DecidableEq α] (G : Finset α) (N : ℕ) (a : α) : ℝ :=
  if a ∈ G then 1 / (N : ℝ) else 0

theorem uniformOn_nonneg {α : Type*} [DecidableEq α] (G : Finset α) (N : ℕ) :
    ∀ a, 0 ≤ uniformOn G N a := by
  intro a
  unfold uniformOn
  split_ifs <;> positivity

theorem uniformOn_mass {α : Type*} [Fintype α] [DecidableEq α]
    (G : Finset α) (N : ℕ) (hN : 0 < N) (hcard : G.card = N) :
    (∑ a, uniformOn G N a) = 1 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [uniformOn, hcard, hNR]

theorem uniformOn_collision {α : Type*} [Fintype α] [DecidableEq α]
    (G : Finset α) (N : ℕ) (hN : 0 < N) (hcard : G.card = N) :
    collision (uniformOn G N) = 1 / (N : ℝ) := by
  have hm := uniformOn_mass G N hN hcard
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  exact (entropy_of_uniform_weights (uniformOn G N) hNR hm (by
    intro a
    unfold uniformOn
    split_ifs <;> simp)).1

theorem uniformOn_distance_bound {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (G : Finset α) (N : ℕ) (hN : 0 < N) (η : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hcard : G.card = N)
    (hclose : ∀ a ∈ G, |(N : ℝ) * w a - 1| ≤ η) :
    (∑ a, |w a - uniformOn G N a|) ≤ (∑ a ∈ Gᶜ, w a) + η := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hgood : ∀ a ∈ G, |w a - 1 / (N : ℝ)| ≤ η / N := by
    intro a ha
    apply (le_div_iff₀ hNR).2
    have hid : (N : ℝ) * (w a - 1 / (N : ℝ)) = (N : ℝ) * w a - 1 := by
      rw [mul_sub, mul_one_div_cancel hNR.ne']
    have he := congrArg abs hid
    rw [abs_mul, abs_of_pos hNR] at he
    nlinarith [hclose a ha]
  have hgoodsum : (∑ a ∈ G, |w a - uniformOn G N a|) ≤ η := by
    calc
      _ = ∑ a ∈ G, |w a - 1 / (N : ℝ)| := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [uniformOn,ha]
      _ ≤ ∑ _a ∈ G, η / (N : ℝ) :=
        Finset.sum_le_sum (fun a ha => hgood a ha)
      _ = η := by
        simp only [Finset.sum_const, nsmul_eq_mul, hcard]
        field_simp
  have hbadsum : (∑ a ∈ Gᶜ, |w a - uniformOn G N a|) = ∑ a ∈ Gᶜ, w a := by
    apply Finset.sum_congr rfl
    intro a ha
    have hnot := Finset.mem_compl.mp ha
    simp [uniformOn, hnot, abs_of_nonneg (hw a)]
  have hpartition := Finset.sum_add_sum_compl G (fun a => |w a - uniformOn G N a|)
  rw [hbadsum] at hpartition
  linarith

theorem integer_abs_lt_one_eq_zero (z : ℤ) (hz : |(z : ℝ)| < 1) : z = 0 := by
  have hlo : (-1 : ℤ) < z := by exact_mod_cast (abs_lt.mp hz).1
  have hhi : z < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hz).2
  omega

/-- Integer-valued moments cannot move by less than one mesh step when the
new measure is uniform on N atoms. -/
theorem uniformOn_exact_sign_moment {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (G : Finset α) (N : ℕ) (hN : 0 < N)
    (p : α → ℤ) (hp : ∀ a, p a = 1 ∨ p a = -1) (t : ℤ)
    (hmoment : (∑ a, w a * (p a : ℝ)) = (t : ℝ))
    (hdistance : (∑ a, |w a - uniformOn G N a|) < 1 / (N : ℝ)) :
    (∑ a, uniformOn G N a * (p a : ℝ)) = (t : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ a, |(uniformOn G N a - w a) * (p a : ℝ)| =
      |w a - uniformOn G N a| := by
    intro a
    rw [abs_mul, abs_sub_comm]
    rcases hp a with h | h <;> simp [h]
  have herror : |(∑ a, uniformOn G N a * (p a : ℝ)) - (t : ℝ)| <
      1 / (N : ℝ) := by
    calc
      _ = |∑ a, (uniformOn G N a - w a) * (p a : ℝ)| := by
        rw [← hmoment]
        simp_rw [sub_mul, Finset.sum_sub_distrib]
      _ ≤ ∑ a, |(uniformOn G N a - w a) * (p a : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a, |w a - uniformOn G N a| := by simp_rw [hterm]
      _ < _ := hdistance
  have hu : (∑ a, uniformOn G N a * (p a : ℝ)) =
      (1 / (N : ℝ)) * (∑ a ∈ G, (p a : ℝ)) := by
    unfold uniformOn
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.mul_sum]
  let z : ℤ := (∑ a ∈ G, p a) - (N : ℤ) * t
  have hz : (z : ℝ) = (N : ℝ) *
      ((∑ a, uniformOn G N a * (p a : ℝ)) - (t : ℝ)) := by
    dsimp [z]
    push_cast
    rw [hu]
    field_simp
  have hzsmall : |(z : ℝ)| < 1 := by
    rw [hz, abs_mul, abs_of_pos hNR]
    have hm := mul_lt_mul_of_pos_left herror hNR
    rw [mul_one_div_cancel hNR.ne'] at hm
    exact hm
  have hzero := integer_abs_lt_one_eq_zero z hzsmall
  have hzcast : (z : ℝ) = 0 := by rw [hzero]; norm_num
  rw [hz] at hzcast
  have hdiff : (∑ a, uniformOn G N a * (p a : ℝ)) - (t : ℝ) = 0 :=
    (mul_eq_zero.mp hzcast).resolve_left hNR.ne'
  exact sub_eq_zero.mp hdiff

theorem near_uniform_omitted_mass {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (N : ℕ) (hN : 8 ≤ N) (hw : ∀ a, 0 ≤ w a)
    (herror : (∑ a, w a * |(N : ℝ) * w a - 1|) < 1 / (8 * (N : ℝ) ^ 2)) :
    (∑ a ∈ (Finset.univ.filter (fun a =>
      |(N : ℝ) * w a - 1| ≤ 1 / (4 * (N : ℝ))))ᶜ, w a) <
      1 / (2 * (N : ℝ)) := by
  classical
  let R : ℝ := N
  let η : ℝ := 1 / (4 * R)
  let G := Finset.univ.filter (fun a => |R * w a - 1| ≤ η)
  have hR : 0 < R := by dsimp [R]; exact_mod_cast (show 0 < N by omega)
  have hη : 0 < η := div_pos zero_lt_one (by positivity)
  have hm := mass_outside_good_set w (fun a => |R * w a - 1|) G η hw
    (fun _ => abs_nonneg _) (by
      intro a ha
      have : ¬|R * w a - 1| ≤ η := by simpa [G] using ha
      exact (lt_of_not_ge this).le)
  have hscale : η * (1 / (2 * R)) = 1 / (8 * R ^ 2) := by
    dsimp [η]
    field_simp
    ring
  apply (mul_lt_mul_iff_right₀ hη).mp
  rw [hscale]
  exact hm.trans_lt herror

theorem near_uniform_distance {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (N : ℕ) (hN : 8 ≤ N)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (herror : (∑ a, w a * |(N : ℝ) * w a - 1|) < 1 / (8 * (N : ℝ) ^ 2)) :
    (∑ a, |w a - uniformOn
      (Finset.univ.filter (fun a => |(N : ℝ) * w a - 1| ≤ 1 / (4 * (N : ℝ)))) N a|) <
      3 / (4 * (N : ℝ)) := by
  classical
  let G := Finset.univ.filter (fun a => |(N : ℝ) * w a - 1| ≤ 1 / (4 * (N : ℝ)))
  change (∑ a, |w a - uniformOn G N a|) < _
  have hcard := near_uniform_support_card w N hN hw hmass herror
  have hbound := uniformOn_distance_bound w G N (by omega) (1 / (4 * (N : ℝ)))
    hw hcard (fun a ha => (Finset.mem_filter.mp ha).2)
  have hbad := near_uniform_omitted_mass w N hN hw herror
  change (∑ a ∈ Gᶜ, w a) < 1 / (2 * (N : ℝ)) at hbad
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (∑ a ∈ Gᶜ, w a) + 1 / (4 * (N : ℝ)) := hbound
    _ < 1 / (2 * (N : ℝ)) + 1 / (4 * (N : ℝ)) := by linarith
    _ = 3 / (4 * (N : ℝ)) := by field_simp; ring

/-- A sufficiently concentrated exact sign frame can be uniformized on its
good support without changing any coordinate moment. -/
theorem near_uniform_exact_isotropy {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (A : α → Fin n → ℤ) (w : α → ℝ) (N : ℕ) (hN : 8 ≤ N)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0)
    (herror : (∑ a, w a * |(N : ℝ) * w a - 1|) < 1 / (8 * (N : ℝ) ^ 2)) :
    ∀ i j, (∑ a, uniformOn (Finset.univ.filter (fun a =>
      |(N : ℝ) * w a - 1| ≤ 1 / (4 * (N : ℝ)))) N a *
        (A a i : ℝ) * (A a j : ℝ)) = if i = j then 1 else 0 := by
  classical
  let G := Finset.univ.filter (fun a => |(N : ℝ) * w a - 1| ≤ 1 / (4 * (N : ℝ)))
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdistance := near_uniform_distance w N hN hw hmass herror
  have hmesh : (3 : ℝ) / (4 * (N : ℝ)) < 1 / (N : ℝ) := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * N)).2
    have hc : (1 / (N : ℝ)) * (4 * (N : ℝ)) = 4 := by field_simp
    rw [hc]
    norm_num
  have hdist : (∑ a, |w a - uniformOn G N a|) < 1 / (N : ℝ) :=
    hdistance.trans hmesh
  intro i j
  have hp : ∀ a, A a i * A a j = 1 ∨ A a i * A a j = -1 := by
    intro a
    rcases hsign a i with h | h <;> rcases hsign a j with h' | h' <;> simp [h,h']
  have hm : (∑ a, w a * ((A a i * A a j : ℤ) : ℝ)) =
      ((if i = j then 1 else 0 : ℤ) : ℝ) := by
    simp only [Int.cast_mul]
    split_ifs with h
    · simpa only [h, ite_true, Int.cast_one, mul_assoc] using hiso i j
    · simpa only [h, ite_false, Int.cast_zero, mul_assoc] using hiso i j
  have hc := uniformOn_exact_sign_moment w G N (by omega)
    (fun a => A a i * A a j) hp (if i = j then 1 else 0) hm hdist
  simp only [Int.cast_mul] at hc
  split_ifs with h
  · simpa only [h, ite_true, Int.cast_one, mul_assoc] using hc
  · simpa only [h, ite_false, Int.cast_zero, mul_assoc] using hc

end EntropyDesigns
