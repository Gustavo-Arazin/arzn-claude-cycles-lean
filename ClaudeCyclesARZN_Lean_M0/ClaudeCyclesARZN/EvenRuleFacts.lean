import ClaudeCyclesARZN.EvenRule

namespace ClaudeCyclesARZN

theorem evenRuleCode_of_le_msub3
    (m i j k : Nat)
    (h : fiberSum m i j k ≤ m - 3) :
    evenRuleCode m i j k = LocalPerm.p012 := by
  simp [evenRuleCode, h]

theorem evenRuleCode_of_eq_msub1
    (m i j k : Nat)
    (hs : fiberSum m i j k = m - 1) :
    evenRuleCode m i j k =
      (if i = half m - 1 ∨ i = half m then LocalPerm.p210 else LocalPerm.p120) := by
  simp [evenRuleCode, hs]

theorem evenRuleCode_of_eq_msub2
    (m i j k : Nat)
    (hs : fiberSum m i j k = m - 2) :
    evenRuleCode m i j k = tauLayerCode m i j := by
  simp [evenRuleCode, hs]

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

theorem tauLayerCode_row0_msub2
    (m : Nat) :
    tauLayerCode m 0 (m - 2) = LocalPerm.p210 := by
  simp [tauLayerCode, half]

theorem tauLayerCode_row0_msub1
    (m : Nat) :
    tauLayerCode m 0 (m - 1) = LocalPerm.p102 := by
  simp [tauLayerCode, half]

theorem tauLayerCode_row1_msub2
    (m : Nat) :
    tauLayerCode m 1 (m - 2) = LocalPerm.p201 := by
  simp [tauLayerCode, half]

theorem tauLayerCode_row1_msub1
    (m : Nat) :
    tauLayerCode m 1 (m - 1) = LocalPerm.p210 := by
  simp [tauLayerCode, half]

end ClaudeCyclesARZN
