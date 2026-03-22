import ClaudeCyclesARZN.EvenRuleTrivialBranchArithmeticTargets

namespace ClaudeCyclesARZN

theorem fiberIndex_val_eq_vertexFiberSum
    (m : Nat) (z : VZ m) :
    (fiberIndex z).val = vertexFiberSum m z := by
  rcases z with ⟨i, j, k⟩
  simp [vertexFiberSum, fiberSum, fiberIndex]

theorem trivialBranchTargetBoundAt_of_vertexFiberSum_le_msub3
    (m : Nat) (z : VZ m)
    (hz : vertexFiberSum m z ≤ m - 3) :
    trivialBranchTargetBoundAt m z := by
  unfold trivialBranchTargetBoundAt
  rw [fiberIndex_val_eq_vertexFiberSum]
  exact hz

theorem canonicalEvenTrivialBranchArithmeticBoundAllTargets
    (m : Nat) :
    ∀ z : VZ m,
      vertexFiberSum m z ≤ m - 3 →
      trivialBranchTargetBoundAt m z := by
  intro z hz
  exact trivialBranchTargetBoundAt_of_vertexFiberSum_le_msub3 m z hz

end ClaudeCyclesARZN
