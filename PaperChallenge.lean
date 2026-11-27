/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Choose
public import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.Push
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Lattice.Lemmas
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Log
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
/-! Paper-level entry for Pairwise-independent designs, entropy, and repair.
The six headline statements below cover entropy instability, sharp entropy bounds
with equality cases, and the impossibility of uniformly bounded observation trades.
The binary-seed bijection is a supporting statement for the concrete definitions.
All declaration text is copied from the previous independent specifications;
only imports, documentation, and unused namespace scaffolding are consolidated.
This new packaging has not been locally compiled, compared, or kernel checked.
See submission/PAPER_ENTRY.json for provenance and verification status. -/
@[expose] public section
namespace EntropyDesigns

noncomputable section

open scoped BigOperators

/-- Encode a Boolean as a sign: true is minus one and false is plus one. -/
def bitSign (b : Bool) : ℤ := if b then -1 else 1

/-- The product of the signs at the coordinates in a finite mask. -/
def walshChar {d : ℕ} (S : Finset (Fin d)) (x : Fin d → Bool) : ℤ :=
  ∏ i ∈ S, bitSign (x i)

/-- The sum of squared weights of a finite law. -/
def collision {α : Type*} [Fintype α] (w : α → ℝ) : ℝ := ∑ a,w a^2

namespace SupportFace

/-- A collection of k Boolean seed vectors, each with s coordinates. -/
abbrev BlockSeeds (k s : ℕ) := Fin k → (Fin s → Bool)

/-- A nonempty subset of the s seed coordinates. -/
abbrev NonzeroMask (s : ℕ) := {S : Finset (Fin s) // S≠∅}

/-- A block index different from the distinguished index i0. -/
abbrev MixedBlock (k : ℕ) (i0 : Fin k) := {j : Fin k // j≠i0}

/-- Observed coordinates: nonconstant characters in each block, together with mixed characters involving i0. -/
abbrev SourceCoordinate (k s : ℕ) (i0 : Fin k) := (Fin k × NonzeroMask s) ⊕ MixedBlock k i0

/-- A Boolean value at every observed coordinate. -/
abbrev SourceOutcome (k s : ℕ) (i0 : Fin k) := SourceCoordinate k s i0 → Bool

/-- Evaluate each within-block Walsh character and each distinguished-block product character. -/
def sourceSign {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x : BlockSeeds k s) :
    SourceCoordinate k s i0 → ℤ :=
  Sum.elim (fun a => walshChar a.2.val (x a.1))
    (fun j => walshChar e (x i0)*walshChar e (x j.val))

/-- Encode the observed sign vector as Booleans, with true denoting minus one. -/
def sourceCode {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x : BlockSeeds k s) : SourceOutcome k s i0 :=
  fun c => decide (sourceSign e i0 x c= -1)

/-- Nonnegative weights with mass one, zero sign means, and zero distinct-coordinate sign correlations. -/
def sourceFeasible {k s : ℕ} (i0 : Fin k) (q : SourceOutcome k s i0 → ℝ) : Prop :=
  (∀ y,0≤q y) ∧ (∑ y,q y=1) ∧
  (∀ c,(∑ y,q y*(bitSign (y c):ℝ))=0) ∧
  (∀ c d,c≠d → (∑ y,q y*(bitSign (y c):ℝ)*(bitSign (y d):ℝ))=0)

/-- The law vanishes outside the observed code image of the block seeds. -/
def sourceSupported {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (q : SourceOutcome k s i0 → ℝ) : Prop :=
  ∀ y,(¬∃ x,sourceCode e i0 x=y) → q y=0

end SupportFace

end

end EntropyDesigns

namespace EntropyDesigns

noncomputable section

open scoped BigOperators

/-- The smallest multiple of four greater than or equal to n. -/
def roundedDimension (n : ℕ) : ℕ := 4*((n+3)/4)

end

end EntropyDesigns

namespace EntropyDesigns

noncomputable section

open scoped BigOperators

/-- Weights equal to the reciprocal cardinality on S, and zero outside S. -/
noncomputable def uniformFiniteLaw {α : Type*} [DecidableEq α] (S : Finset α) (x : α) : ℝ :=
  if x∈S then 1/(S.card : ℝ) else 0

/-- Half the sum of absolute differences of finite weights. -/
noncomputable def totalVariation {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1/2 : ℝ)*(∑ x,|p x-q x|)

namespace SupportWitness

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every pair of distinct elements of the finite set satisfies relation R. -/
def IsClique (R : α → α → Prop) (T : Finset α) : Prop :=
  ∀ a∈T,∀ b∈T,a≠b → R a b

/-- Uniform laws on n-element subsets whose distinct elements satisfy R. -/
def blockLaws (R : α → α → Prop) (n : ℕ) : Set (α → ℝ) :=
  {q | ∃ T : Finset α,T.card=n ∧ IsClique R T ∧ q=uniformFiniteLaw T}

end SupportWitness

namespace SupportFace

open Filter

open scoped Topology

/-- The sign inner product after prepending a constant coordinate is zero. -/
def observedOrthogonal {k s : ℕ} {i0 : Fin k} (x y : SourceOutcome k s i0) : Prop :=
  1+(∑ c : SourceCoordinate k s i0,bitSign (x c)*bitSign (y c))=0

end SupportFace

/-- Map a Boolean vector to the binary field coordinatewise, sending true to one. -/
def binarySeed {d : ℕ} (x : Fin d → Bool) : Fin d → ZMod 2 :=
  fun i => if x i then 1 else 0

/-- The Boolean-to-binary-field coordinate map is bijective; this supports the concrete field coordinate definitions. -/
theorem binarySeed_bijective {d : ℕ} : Function.Bijective (@binarySeed d) := by sorry

namespace SupportFace

/-- The equivalence between Boolean vectors and vectors over the field with two elements. -/
def boolBinaryEquiv (s : ℕ) : (Fin s → Bool) ≃ (Fin s → ZMod 2) :=
  Equiv.ofBijective binarySeed binarySeed_bijective

/-- A chosen linear coordinate isomorphism from the degree-s binary field to s binary coordinates. -/
def fieldCoordinates (s : ℕ) (hs : s≠0) : GaloisField 2 s ≃ₗ[ZMod 2] (Fin s → ZMod 2) :=
  LinearEquiv.ofFinrankEq (R:=ZMod 2) (GaloisField 2 s) (Fin s → ZMod 2)
    (by rw [GaloisField.finrank 2 hs,Module.finrank_fin_fun])

/-- Express a finite-field element as a Boolean vector using the chosen linear coordinates. -/
def fieldSeedEquiv (s : ℕ) (hs : s≠0) : GaloisField 2 s ≃ (Fin s → Bool) :=
  (fieldCoordinates s hs).toEquiv.trans (boolBinaryEquiv s).symm

section

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- The binary-linear map sending the pair (A,B) to A plus t times B. -/
def slopeMap (t : F) : (F × F) →ₗ[ZMod 2] F where
  toFun p := p.1+t*p.2
  map_add' p q := by simp [mul_add];ring
  map_smul' c p := by simp [Algebra.smul_def];ring

end

/-- Evaluate the chosen finite-field slopes on a pair of field elements and encode each value as a Boolean seed. -/
def fieldSlopeSeeds {k s : ℕ} (hs : s≠0) (t : Fin k → GaloisField 2 s)
    (p : GaloisField 2 s × GaloisField 2 s) : BlockSeeds k s :=
  fun i => fieldSeedEquiv s hs (slopeMap (t i) p)

end SupportFace

namespace ConcentratedFamily

open SupportFace Filter

open scoped Topology

/-- Observed outcomes produced by pairs of finite-field parameters at the selected slopes. -/
def planeSupport {k s : ℕ} (hs : s≠0) (e : Finset (Fin s)) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) : Finset (SourceOutcome k s i0) := by
  classical
  exact Finset.univ.filter (fun y => ∃ p : GaloisField 2 s × GaloisField 2 s,
    sourceCode e i0 (fieldSlopeSeeds hs t p)=y)

end ConcentratedFamily

end

end EntropyDesigns

namespace EntropyDesigns

open scoped BigOperators

/-- Shannon entropy, defined as minus the sum of weight times logarithm of weight. -/
noncomputable def shannon {α : Type*} [Fintype α] (w : α → ℝ) : ℝ :=
  -(∑ a, w a * Real.log (w a))

end EntropyDesigns

namespace EntropyDesigns.RelativeSequence

noncomputable section

open SupportFace ConcentratedFamily

open Filter Set

open scoped Topology BigOperators

/-- The Renyi logarithmic power-sum formula used away from order one. -/
def renyiOffOne {A : Type*} [Fintype A] (w : A → ℝ) (α : ℝ) : ℝ :=
  Real.log (∑ x, (w x)^α) / (1-α)

/-- Renyi entropy with its order-one branch defined to be Shannon entropy. -/
def renyiEntropy {A : Type*} [Fintype A] (w : A → ℝ) (α : ℝ) : ℝ :=
  if α = 1 then shannon w else renyiOffOne w α

/-- The largest weight on the finite nonempty outcome space. -/
def maxWeight {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty w

/-- Minus the logarithm of the largest weight. -/
def minEntropy {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ) : ℝ :=
  -Real.log (maxWeight w)

/-- Concrete finite-field law data together with proofs of feasibility, strict local collision maximality, extreme-point status, an optimal law, and exact entropy and total-variation formulas. The existence theorem below constructs these data rather than assuming them. -/
structure CompleteLawData (k s : ℕ) where
  e : Finset (Fin s)
  he : e.Nonempty
  i0 : Fin k
  hs : s≠0
  t : Fin k → GaloisField 2 s
  ht : Function.Injective t
  properties :
    let p := uniformFiniteLaw (planeSupport hs e i0 t);
          sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
            (planeSupport hs e i0 t).card=(2^s)^2 ∧ collision p=1/((2:ℝ)^s)^2 ∧
            (0<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) ∧
              ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → q≠p →
                ‖q-p‖<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) → collision q<collision p) ∧
            (∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
              (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) ∧
              collision p/collision q=(k:ℝ)/(2:ℝ)^s) ∧
            (∀ q : SourceOutcome k s i0 → ℝ,
              q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
                1-1/(k:ℝ)≤totalVariation p q) ∧
            (∃ q : SourceOutcome k s i0 → ℝ,
              q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
                totalVariation p q=1-1/(k:ℝ))

  vertex : uniformFiniteLaw (planeSupport hs e i0 t) ∈
    Set.extremePoints ℝ {q : SourceOutcome k s i0 → ℝ | sourceFeasible i0 q}
  optimizer : SourceOutcome k s i0 → ℝ
  optimizer_feasible : sourceFeasible i0 optimizer
  optimizer_collision : collision optimizer=1/((k*2^s:ℕ):ℝ)
  optimizer_global : ∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision optimizer
  ratio : collision (uniformFiniteLaw (planeSupport hs e i0 t))/collision optimizer=(k:ℝ)/(2:ℝ)^s
  entropy_optimizer : ∀ α : ℝ,0<α → renyiEntropy optimizer α=Real.log ((k*2^s:ℕ):ℝ)
  minentropy_optimizer : minEntropy optimizer=Real.log ((k*2^s:ℕ):ℝ)
  entropy_excess : ∀ α : ℝ,0<α →
    renyiEntropy (uniformFiniteLaw (planeSupport hs e i0 t)) α-renyiEntropy optimizer α=
      Real.log ((2:ℝ)^s/(k:ℝ))
  minentropy_excess : minEntropy (uniformFiniteLaw (planeSupport hs e i0 t))-minEntropy optimizer=
    Real.log ((2:ℝ)^s/(k:ℝ))

/-- The uniform law on the observed finite-field support specified by the data. -/
def CompleteLawData.law {k s : ℕ} (D : CompleteLawData k s) : SourceOutcome k s D.i0 → ℝ :=
  uniformFiniteLaw (planeSupport D.hs D.e D.i0 D.t)

/-- An unconditional sequence of exact pairwise-independent laws has asymptotically optimal collision and all positive-order Renyi entropies, but total variation distance from every Hadamard mixture tends to one. The data also certify strict local maxima and vertices. -/
theorem full_unconditional_sequence :
    ∃ a s : ℕ → ℕ, ∃ D : (i : ℕ) → CompleteLawData (12^(a i)) (s i),
      Tendsto (fun i => 12^(a i)*2^(s i)) atTop atTop ∧
      (∀ i, ∃ H : Matrix (Fin (12^(a i)*2^(s i))) (Fin (12^(a i)*2^(s i))) ℤ,
        Matrix.IsHadamard H) ∧
      (∀ i, sourceFeasible (D i).i0 (D i).law ∧
        (D i).law ∈ Set.extremePoints ℝ
          {q : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ | sourceFeasible (D i).i0 q}) ∧
      Tendsto (fun i => collision (D i).law / collision (D i).optimizer) atTop (nhds 1) ∧
      Tendsto (fun i => ((12^(a i)*2^(s i):ℕ):ℝ) * collision (D i).law) atTop (nhds 1) ∧
      (∀ i, ∀ q : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (12^(a i)*2^(s i))) →
          1-1/((12^(a i):ℕ):ℝ) ≤ totalVariation (D i).law q) ∧
      (∀ i, ∃ q : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (12^(a i)*2^(s i))) ∧
          totalVariation (D i).law q=1-1/((12^(a i):ℕ):ℝ)) ∧
      Tendsto (fun i => 1-1/((12^(a i):ℕ):ℝ)) atTop (nhds 1) ∧
      (∀ α : ℝ, 0<α →
        (∀ i, ∀ w : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ,
          sourceFeasible (D i).i0 w → renyiEntropy (D i).optimizer α ≤ renyiEntropy w α) ∧
        Tendsto (fun i => renyiEntropy (D i).law α-renyiEntropy (D i).optimizer α)
          atTop (nhds 0)) ∧
      (∀ i, ∀ w : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ,
        sourceFeasible (D i).i0 w → minEntropy (D i).optimizer ≤ minEntropy w) ∧
      Tendsto (fun i => minEntropy (D i).law-minEntropy (D i).optimizer) atTop (nhds 0) := by sorry

end

end EntropyDesigns.RelativeSequence

namespace EntropyDesigns.DenominatorTrades

noncomputable section

/- A reduced observation trade written in normalized sign coordinates.
The final two fields preserve precisely the moments of degrees one and two. -/

/-- Two normalized sign arrays agree outside S, have disjoint removed and inserted rows, and preserve all first and second moments of the nonconstant coordinates. -/
def IsReducedNormalizedObservationTrade {J : Type*} [Fintype J]
    (A B : Matrix J J ℤ) (c₀ : J) (S : Finset J) : Prop :=
  (∀ r,A r c₀=1) ∧ (∀ r,B r c₀=1) ∧
  (∀ r c,B r c=1 ∨ B r c= -1) ∧
  (∀ r,r∉S → B r=A r) ∧
  (∀ r,r∈S → ∀ t,t∈S → B r≠A t) ∧
  (∀ c,c≠c₀ → (∑ r,B r c)=(∑ r,A r c)) ∧
  (∀ c d,c≠c₀ → d≠c₀ → (∑ r,B r c*B r d)=(∑ r,A r c*A r d))

end

end EntropyDesigns.DenominatorTrades

namespace EntropyDesigns.PrimeExponentRigidity

noncomputable section

/- Every normalized sign-coordinate observation fiber at this order is
isolated under reduced degree-two-moment-preserving moves of degree at most R. -/

/-- Every reduced normalized trade from any Hadamard array at this order, replacing at most R observations, has an empty replacement set. -/
def IsRigidOrderAtDegree (n R : ℕ) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) ℤ,∀ c₀ : Fin n,∀ S : Finset (Fin n),
    A.IsHadamard → DenominatorTrades.IsReducedNormalizedObservationTrade A B c₀ S →
    S.card≤R → S=∅

/-- For any replacement budget R, infinitely many Hadamard orders congruent to four modulo eight are rigid for every normalized observation array. -/
theorem infinitely_many_known_rigid_orders (R : ℕ) :
    Set.Infinite {n : ℕ | n%8=4 ∧
      (∃ A : Matrix (Fin n) (Fin n) ℤ,A.IsHadamard) ∧ IsRigidOrderAtDegree n R} := by
  sorry

end

end EntropyDesigns.PrimeExponentRigidity

open Filter

open scoped Topology

namespace EntropyDesigns

open scoped symmDiff

/-- Minus the logarithm of collision probability. -/
noncomputable def collisionEntropy {α : Type*} [Fintype α] (w : α → ℝ) : ℝ :=
  -Real.log (collision w)

/-- Prepend a constant sign coordinate equal to one. -/
def augmentedSign {α : Type*} {d : ℕ} (x : α → Fin d → ℤ) (a : α) :
    Fin (d + 1) → ℤ := Fin.cases 1 (x a)

/-- Sharp collision, collision-entropy, and Shannon-entropy bounds for unbiased pairwise-independent sign laws in every dimension. -/
theorem sharp_sign_cube_entropy_bounds {d : ℕ} (hd : 2 ≤ d) (w : (Fin d → Bool) → ℝ) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hmean : ∀ i, ∑ a, w a * (bitSign (a i) : ℝ) = 0) (hpair : ∀ i j, i ≠ j → ∑ a, w a * (bitSign (a i) : ℝ) * (bitSign (a j) : ℝ) = 0) : collision w ≤ 1 / (roundedDimension (d + 1) : ℝ) ∧ Real.log (roundedDimension (d + 1)) ≤ collisionEntropy w ∧ Real.log (roundedDimension (d + 1)) ≤ shannon w := by sorry

/-- Collision equality forces a uniform law on the rounded number of atoms and a Hadamard completion retaining their augmented coordinates. -/
theorem sharp_sign_cube_equality_completion {d : ℕ} (hd : 2 ≤ d) (w : (Fin d → Bool) → ℝ) (hw : ∀ b, 0 ≤ w b) (hmass : ∑ b, w b = 1) (hmean : ∀ i, ∑ b, w b * (bitSign (b i) : ℝ) = 0) (hpair : ∀ i j, i ≠ j → ∑ b, w b * (bitSign (b i) : ℝ) * (bitSign (b j) : ℝ) = 0) (heq : collision w = 1 / (roundedDimension (d + 1) : ℝ)) : (∀ b, w b = 0 ∨ w b = 1 / (roundedDimension (d + 1) : ℝ)) ∧ (Finset.univ.filter (fun b => w b ≠ 0)).card = roundedDimension (d + 1) ∧ ∃ (H : Matrix (Fin (roundedDimension (d + 1))) (Fin (roundedDimension (d + 1))) ℝ) (columns : Fin (d + 1) ↪ Fin (roundedDimension (d + 1))) (rows : {b // w b ≠ 0} ≃ Fin (roundedDimension (d + 1))), Matrix.IsHadamard H ∧ ∀ b i, H (rows b) (columns i) = (augmentedSign (fun (b : Fin d → Bool) i => bitSign (b i)) (b : Fin d → Bool) i : ℝ) := by sorry

/-- Attainment of the sharp collision bound is equivalent to Hadamard existence at the rounded order. -/
theorem collision_attainment_iff_hadamard {d : ℕ} (hd : 2 ≤ d) : (∃ w : (Fin d → Bool) → ℝ, (∀ b, 0 ≤ w b) ∧ (∑ b, w b = 1) ∧ (∀ i, ∑ b, w b * (bitSign (b i) : ℝ) = 0) ∧ (∀ i j, i ≠ j → ∑ b, w b * (bitSign (b i) : ℝ) * (bitSign (b j) : ℝ) = 0) ∧ collision w = 1 / (roundedDimension (d + 1) : ℝ)) ↔ ∃ H : Matrix (Fin (roundedDimension (d + 1))) (Fin (roundedDimension (d + 1))) ℝ, Matrix.IsHadamard H := by sorry

/-- Attainment of the sharp Shannon entropy bound is equivalent to Hadamard existence at the rounded order. -/
theorem entropy_attainment_iff_hadamard {d : ℕ} (hd : 2 ≤ d) : (∃ w : (Fin d → Bool) → ℝ, (∀ b, 0 ≤ w b) ∧ (∑ b, w b = 1) ∧ (∀ i, ∑ b, w b * (bitSign (b i) : ℝ) = 0) ∧ (∀ i j, i ≠ j → ∑ b, w b * (bitSign (b i) : ℝ) * (bitSign (b j) : ℝ) = 0) ∧ (collisionEntropy w = Real.log (roundedDimension (d + 1)) ∨ shannon w = Real.log (roundedDimension (d + 1)))) ↔ ∃ H : Matrix (Fin (roundedDimension (d + 1))) (Fin (roundedDimension (d + 1))) ℝ, Matrix.IsHadamard H := by sorry

end EntropyDesigns
