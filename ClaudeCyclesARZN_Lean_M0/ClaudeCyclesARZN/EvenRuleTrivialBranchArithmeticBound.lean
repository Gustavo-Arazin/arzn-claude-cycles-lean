import ClaudeCyclesARZN.EvenRuleTrivialBranchArithmeticTargets

namespace ClaudeCyclesARZN

theorem fiberIndex_val_eq_vertexFiberSum
    (m : Nat) (hm : admissibleEvenM m) (z : VZ m) :
    (fiberIndex z).val = vertexFiberSum m z := by
  letI : NeZero m := ⟨by
    rcases hm with ⟨hm8, _⟩
    omega⟩
  rcases z with ⟨i, j, k⟩
  unfold vertexFiberSum fiberSum fiberIndex
  have hcast :
      (i + j + k : ZMod m) = (((i.val + j.val + k.val : Nat)) : ZMod m) := by
    rw [← ZMod.natCast_zmod_val i, ← ZMod.natCast_zmod_val j, ← ZMod.natCast_zmod_val k]
    simp [Nat.cast_add, add_assoc]
  have hval :
      (i + j + k : ZMod m).val =
      ((((i.val + j.val + k.val : Nat)) : ZMod m)).val := by
    exact congrArg ZMod.val hcast
  have hnat :
      ((((i.val + j.val + k.val : Nat)) : ZMod m)).val =
      (i.val + j.val + k.val) % m := by
    simp
  exact hval.trans hnat

theorem trivialBranchTargetBoundAt_of_vertexFiberSum_le_msub3
    (m : Nat) (hm : admissibleEvenM m) (z : VZ m)
    (hz : vertexFiberSum m z ≤ m - 3) :
    trivialBranchTargetBoundAt m z := by
  unfold trivialBranchTargetBoundAt
  rw [fiberIndex_val_eq_vertexFiberSum m hm z]
  exact hz

theorem canonicalEvenTrivialBranchArithmeticBoundAllTargets
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ z : VZ m,
      vertexFiberSum m z ≤ m - 3 →
      trivialBranchTargetBoundAt m z := by
  intro z hz
  exact trivialBranchTargetBoundAt_of_vertexFiberSum_le_msub3 m hm z hz

end ClaudeCyclesARZN
