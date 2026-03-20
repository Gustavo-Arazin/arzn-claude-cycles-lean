import ClaudeCyclesARZN.EvenRuleFacts

namespace ClaudeCyclesARZN

def exceptionalFiberProp (m i j k : Nat) : Prop :=
  fiberSum m i j k = m - 2 ∨ fiberSum m i j k = m - 1

theorem isExceptionalFiber_eq_true_iff
    (m s : Nat) :
    isExceptionalFiber m s = true ↔ s = m - 2 ∨ s = m - 1 := by
  unfold isExceptionalFiber
  by_cases h1 : s = m - 2
  · simp [h1]
  · by_cases h2 : s = m - 1
    · simp [h1, h2]
    · simp [h1, h2]

theorem isExceptionalFiber_eq_false_iff
    (m s : Nat) :
    isExceptionalFiber m s = false ↔ s ≠ m - 2 ∧ s ≠ m - 1 := by
  unfold isExceptionalFiber
  by_cases h1 : s = m - 2
  · simp [h1]
  · by_cases h2 : s = m - 1
    · simp [h1, h2]
    · simp [h1, h2]

theorem exceptionalFiberProp_iff_bool
    (m i j k : Nat) :
    exceptionalFiberProp m i j k ↔ isExceptionalFiber m (fiberSum m i j k) = true := by
  unfold exceptionalFiberProp
  rw [isExceptionalFiber_eq_true_iff]

theorem not_exceptional_of_le_msub3
    (m s : Nat)
    (hm : 8 ≤ m)
    (hs : s ≤ m - 3) :
    isExceptionalFiber m s = false := by
  unfold isExceptionalFiber
  have hneq1 : s ≠ m - 2 := by
    omega
  have hneq2 : s ≠ m - 1 := by
    omega
  simp [hneq1, hneq2]

theorem fiberSum_le_msub3_of_not_exceptional
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hfalse : isExceptionalFiber m (fiberSum m i j k) = false) :
    fiberSum m i j k ≤ m - 3 := by
  rcases hm with ⟨hm8, _⟩
  have hmpos : 0 < m := by
    omega
  have hs_lt : fiberSum m i j k < m := by
    unfold fiberSum
    exact Nat.mod_lt _ hmpos
  have hneq1 : fiberSum m i j k ≠ m - 2 := by
    intro hEq
    have htrue : isExceptionalFiber m (fiberSum m i j k) = true := by
      exact isExceptionalFiber_of_eq_msub2 m (fiberSum m i j k) hEq
    rw [hfalse] at htrue
    cases htrue
  have hneq2 : fiberSum m i j k ≠ m - 1 := by
    intro hEq
    have htrue : isExceptionalFiber m (fiberSum m i j k) = true := by
      exact isExceptionalFiber_of_eq_msub1 m (fiberSum m i j k) hEq
    rw [hfalse] at htrue
    cases htrue
  omega

theorem evenRuleCode_of_not_exceptional
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hfalse : isExceptionalFiber m (fiberSum m i j k) = false) :
    evenRuleCode m i j k = LocalPerm.p012 := by
  apply evenRuleCode_of_le_msub3
  exact fiberSum_le_msub3_of_not_exceptional m i j k hm hfalse

end ClaudeCyclesARZN
