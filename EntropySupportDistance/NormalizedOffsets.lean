/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.DisjointCompletions
public import EntropySupportFace.SourceConsequences
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section

abbrev OffsetParameters (k s : ℕ) (i0 : Fin k) := MixedBlock k i0 → (Fin s → Bool)

def extendOffsets {k s : ℕ} (i0 : Fin k) (c : OffsetParameters k s i0) : BlockSeeds k s :=
  fun j => if h : j=i0 then (fun _ => false) else c ⟨j,h⟩

theorem extendOffsets_zero {k s : ℕ} (i0 : Fin k) (c : OffsetParameters k s i0) :
    extendOffsets i0 c i0=fun _ => false := by simp [extendOffsets]

theorem extendOffsets_injective {k s : ℕ} (i0 : Fin k) :
    Function.Injective (extendOffsets (s:=s) i0) := by
  intro c d h
  funext j
  have hj := congrFun h j.val
  simpa [extendOffsets,j.property] using hj

def offsetPartitionEquiv {k s : ℕ} (i0 : Fin k) :
    (OffsetParameters k s i0 × (Fin s → Bool)) ≃ BlockSeeds k s where
  toFun p := offsetSeed (extendOffsets i0 p.1) p.2
  invFun x := (fun j => seedXor (x j.val) (x i0),x i0)
  left_inv p := by
    rcases p with ⟨c,a⟩
    apply Prod.ext
    · funext j t
      cases ha : a t <;> cases hc : c j t <;>
        simp [offsetSeed,seedXor,extendOffsets,j.property,ha,hc]
    · funext t
      cases ha : a t <;> simp [offsetSeed,seedXor,extendOffsets,ha]
  right_inv x := by
    funext j t
    by_cases hj : j=i0
    · subst j
      cases hx : x i0 t <;> simp [offsetSeed,seedXor,extendOffsets,hx]
    · cases ha : x i0 t <;> cases hb : x j t <;>
        simp [offsetSeed,seedXor,extendOffsets,hj,ha,hb]

theorem card_offset_parameters {k s : ℕ} (i0 : Fin k) :
    Fintype.card (OffsetParameters k s i0)=(2^s)^(k-1) := by
  simp only [OffsetParameters,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,card_mixed_blocks]

theorem normalized_completed_rows_injective {k s : ℕ} (hs : 2≤s)
    (e : Finset (Fin s)) (i0 : Fin k) (K : Matrix (Fin k) (Fin k) ℤ)
    (hK : Matrix.IsHadamard K) : Function.Injective
      (fun p : OffsetParameters k s i0 × (Fin k × (Fin s → Bool)) =>
        completedOffsetRow e i0 (extendOffsets i0 p.1) (fun i j => K i j) p.2.1 p.2.2) := by
  intro p q heq
  obtain ⟨hc,ht,ha⟩ := completed_rows_globally_injective hs e i0 K hK
    (extendOffsets i0 p.1) (extendOffsets i0 q.1)
    (extendOffsets_zero i0 p.1) (extendOffsets_zero i0 q.1) p.2.1 q.2.1 p.2.2 q.2.2 heq
  exact Prod.ext (extendOffsets_injective i0 hc) (Prod.ext ht ha)

end
end EntropyDesigns.SupportFace
