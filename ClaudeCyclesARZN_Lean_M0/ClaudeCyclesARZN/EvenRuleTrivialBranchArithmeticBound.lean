import ClaudeCyclesARZN.EvenRuleTrivialBranchArithmeticTargets

namespace ClaudeCyclesARZN

theorem trivialBranchTargetBoundAt_of_vertexFiberSum_le_msub3
    (m : Nat) (z : VZ m)
    (hz : vertexFiberSum m z ≤ m - 3) :
    trivialBranchTargetBoundAt m z := by
  exact hz

theorem canonicalEvenTrivialBranchArithmeticBoundAllTargets
    (m : Nat) :
    ∀ z : VZ m,
      vertexFiberSum m z ≤ m - 3 →
      trivialBranchTargetBoundAt m z := by
  intro z hz
  exact trivialBranchTargetBoundAt_of_vertexFiberSum_le_msub3 m z hz

end ClaudeCyclesARZN
