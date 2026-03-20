import ClaudeCyclesARZN.EvenRule

namespace ClaudeCyclesARZN

theorem evenRuleCode_of_le_msub3
    (m i j k : Nat)
    (h : fiberSum m i j k ≤ m - 3) :
    evenRuleCode m i j k = LocalPerm.p012 := by
  unfold evenRuleCode
  simp [h]

theorem evenRuleCode_of_eq_msub1
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hs : fiberSum m i j k = m - 1) :
    evenRuleCode m i j k =
      (if i = half m - 1 ∨ i = half m then LocalPerm.p210 else LocalPerm.p120) := by
  rcases hm with ⟨hm8, hEven⟩
  unfold evenRuleCode
  rw [hs]
  have hlt : ¬ (m - 1 ≤ m - 3) := by
    omega
  simp [hlt]

theorem evenRuleCode_of_eq_msub2
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hs : fiberSum m i j k = m - 2) :
    evenRuleCode m i j k = tauLayerCode m i j := by
  rcases hm with ⟨hm8, hEven⟩
  unfold evenRuleCode
  rw [hs]
  have hlt : ¬ (m - 2 ≤ m - 3) := by
    omega
  have hneq : ¬ (m - 2 = m - 1) := by
    omega
  simp [hlt, hneq]

theorem isExceptionalFiber_of_eq_msub2
    (m s : Nat)
    (hs : s = m - 2) :
    isExceptionalFiber m s = true := by
  simp [isExceptionalFiber, hs]

theorem isExceptionalFiber_of_eq_msub1
    (m s : Nat)
    (hs : s = m - 1) :
    isExceptionalFiber m s = true := by
  simp [isExceptionalFiber, hs]

end ClaudeCyclesARZN
