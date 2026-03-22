import ClaudeCyclesARZN.EvenRuleTrivialBranchArithmeticTargets

namespace ClaudeCyclesARZN

theorem fiberIndex_val_eq_vertexFiberSum
    (m : Nat) (z : VZ m) :
    (fiberIndex z).val = vertexFiberSum m z := by
  apply ZMod.val_injective
  rcases z with ⟨i, j, k⟩
  change i + j + k = (((i.val + j.val + k.val) % m : Nat) : ZMod m)
  rw [Nat.cast_mod]
  simp [vertexFiberSum, fiberSum, fiberIndex, add_assoc]

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
