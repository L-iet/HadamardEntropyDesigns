/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentratedFamily.FieldSeedAddition
public import EntropySupportFace.FieldObservables
public import EntropySupportDistance.NormalizedOffsets
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.ConcentratedFamily
noncomputable section
open SupportFace

def fieldOffsetParameters {k s : ℕ} (hs : s≠0) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (B : GaloisField 2 s) : OffsetParameters k s i0 :=
  fun j => fieldSeedEquiv s hs ((t j.val-t i0)*B)

theorem extend_fieldOffsetParameters {k s : ℕ} (hs : s≠0) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (B : GaloisField 2 s) (j : Fin k) :
    extendOffsets i0 (fieldOffsetParameters hs i0 t B) j=
      fieldSeedEquiv s hs ((t j-t i0)*B) := by
  classical
  by_cases hj : j=i0
  · subst j
    simp [extendOffsets,fieldSeedEquiv_zero]
  · simp [extendOffsets,fieldOffsetParameters,hj]

theorem fieldSlopeSeeds_offset_identity {k s : ℕ} (hs : s≠0) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (A B : GaloisField 2 s) :
    offsetSeed (extendOffsets i0 (fieldOffsetParameters hs i0 t B))
      (fieldSeedEquiv s hs (A+t i0*B))=fieldSlopeSeeds hs t (A,B) := by
  funext j
  change seedXor (fieldSeedEquiv s hs (A+t i0*B))
    (extendOffsets i0 (fieldOffsetParameters hs i0 t B) j)=
      fieldSeedEquiv s hs (A+t j*B)
  rw [extend_fieldOffsetParameters,fieldSeedEquiv_xor]
  congr 1
  ring

theorem fieldOffsetParameters_injective {k s : ℕ} (hk : 2≤k) (hs : s≠0) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    Function.Injective (fieldOffsetParameters hs i0 t) := by
  intro B C h
  let a : Fin k := ⟨0,by omega⟩
  let b : Fin k := ⟨1,by omega⟩
  have hab : a≠b := by intro he;have hv := congrArg Fin.val he;change 0=1 at hv;omega
  obtain ⟨j,hj⟩ : ∃ j : Fin k,j≠i0 := by
    by_cases ha : a=i0
    · exact ⟨b,fun hb => hab (ha.trans hb.symm)⟩
    · exact ⟨a,ha⟩
  have hv := congrFun h ⟨j,hj⟩
  change fieldSeedEquiv s hs ((t j-t i0)*B)=fieldSeedEquiv s hs ((t j-t i0)*C) at hv
  have heq := (fieldSeedEquiv s hs).injective hv
  have hdiff : t j-t i0≠0 := sub_ne_zero.mpr (fun he => hj (ht he))
  have hz : (t j-t i0)*(B-C)=0 := by
    calc
      _=(t j-t i0)*B-(t j-t i0)*C := by ring
      _=0 := sub_eq_zero.mpr heq
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hdiff)

end
end EntropyDesigns.ConcentratedFamily
