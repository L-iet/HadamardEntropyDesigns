/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyProjectInstability.UnconditionalBudget
@[expose] public section
namespace EntropyDesigns.ProjectInstability
open Filter Asymptotics RelativeSequence GapTransfer
open scoped Topology
noncomputable section

/-- One actual unconditional family, with a law at EVERY large dyadic
exponent and exactly the explicit dyadic arithmetic buffer. -/
structure DyadicLawFamily where
  T : ℕ → ℕ
  base : ℕ
  D : (i : ℕ) → CompleteLawData (2^(base+i)-2^(bufferExponent T (base+i))) (base+i)
  known : ∀ i,knownHadamardOrder (2^(base+i)-2^(bufferExponent T (base+i)))
  small : ∀ i,bufferExponent T (base+i)+2<base+i ∧
    2^(bufferExponent T (base+i))<2^(base+i)/2
  ratio : Tendsto (fun i => ((2^(base+i)-2^(bufferExponent T (base+i)):ℕ):ℝ)/(2:ℝ)^(base+i)) atTop (nhds 1)
  loggap : Tendsto (fun i => Real.log ((2:ℝ)^(bufferExponent T (base+i)))/Real.log ((2:ℝ)^(base+i))) atTop (nhds 0)

def DyadicLawFamily.seedOrder (F : DyadicLawFamily) (i : ℕ) : ℕ := 2^(F.base+i)
def DyadicLawFamily.gapOrder (F : DyadicLawFamily) (i : ℕ) : ℕ := 2^(bufferExponent F.T (F.base+i))
def DyadicLawFamily.lowOrder (F : DyadicLawFamily) (i : ℕ) : ℕ := F.seedOrder i-F.gapOrder i

theorem dyadic_law_family_exists : Nonempty DyadicLawFamily := by
  classical
  obtain ⟨T,hT,hr,hg,hlaws⟩ := unconditional_buffered_laws
  obtain ⟨S,hS⟩ := eventually_atTop.1 (hlaws.and (buffer_exponent_eventually_small T hT))
  have hpoint (i : ℕ) := hS (S+i) (Nat.le_add_right S i)
  let D : (i : ℕ) → CompleteLawData (2^(S+i)-2^(bufferExponent T (S+i))) (S+i) :=
    fun i => Classical.choice (hpoint i).1.2.1
  have hindex : Tendsto (fun i : ℕ => S+i) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_add_left i S) tendsto_id
  exact ⟨{ T := T
           base := S
           D := D
           known := fun i => (hpoint i).1.1
           small := fun i => (hpoint i).2
           ratio := by simpa only [Function.comp_def] using hr.comp hindex
           loggap := by simpa only [Function.comp_def] using hg.comp hindex }⟩

theorem dyadic_family_orders (F : DyadicLawFamily) (i : ℕ) :
    0<F.lowOrder i ∧ F.lowOrder i<F.seedOrder i ∧
    0<F.gapOrder i ∧ F.seedOrder i-F.lowOrder i=F.gapOrder i ∧
    F.seedOrder i<2*F.lowOrder i := by
  have hp : 0<F.seedOrder i := pow_pos (by decide) _
  have hg : 0<F.gapOrder i := pow_pos (by decide) _
  have hs := (F.small i).2
  change F.gapOrder i<F.seedOrder i/2 at hs
  dsimp [DyadicLawFamily.lowOrder]
  omega

theorem dyadic_family_cast_identity (F : DyadicLawFamily) (i : ℕ) :
    (F.lowOrder i:ℝ)=(F.seedOrder i:ℝ)-(F.gapOrder i:ℝ) := by
  apply Nat.cast_sub
  have hs := (dyadic_family_orders F i).2.1
  have hg := (dyadic_family_orders F i).2.2.2.1
  omega

end
end EntropyDesigns.ProjectInstability
