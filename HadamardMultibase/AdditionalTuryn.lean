/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Golay-family lemma from the licensed first project; generic product proof reused unchanged. -/
module
public import HadamardMultibase.Turyn
public import HadamardMultibase.AdditionalSeeds
@[expose] public section
namespace HadamardMultibase
theorem golayFamily : GolayFamily := fun a b =>
  (golayLength_two.pow a).mul (golayLength_ten.pow b)
end HadamardMultibase
