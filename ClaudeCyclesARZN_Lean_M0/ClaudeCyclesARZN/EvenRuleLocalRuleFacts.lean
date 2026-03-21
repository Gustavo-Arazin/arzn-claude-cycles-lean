import ClaudeCyclesARZN.EvenRuleLocalRule

namespace ClaudeCyclesARZN

theorem evenRuleLocalRule_of_not_residualSupport
    (m : Nat) (v : VZ m) (hm : admissibleEvenM m) (c : Color)
    (hfalse : residualSupport m v.1.val v.2.1.val v.2.2.val = false) :
    evenRuleLocalRule m v c = axisOfLocalPerm LocalPerm.p012 c := by
  unfold evenRuleLocalRule evenRuleAxis
  rw [evenRuleCode_of_not_residualSupport
        m v.1.val v.2.1.val v.2.2.val hm hfalse]

theorem evenRuleLocalRule_of_eq_msub2
    (m : Nat) (v : VZ m) (hm : admissibleEvenM m) (c : Color)
    (hs : fiberSum m v.1.val v.2.1.val v.2.2.val = m - 2) :
    evenRuleLocalRule m v c =
      axisOfLocalPerm (tauLayerCode m v.1.val v.2.1.val) c := by
  unfold evenRuleLocalRule evenRuleAxis
  rw [evenRuleCode_of_eq_msub2
        m v.1.val v.2.1.val v.2.2.val hm hs]

theorem evenRuleLocalRule_of_eq_msub1
    (m : Nat) (v : VZ m) (hm : admissibleEvenM m) (c : Color)
    (hs : fiberSum m v.1.val v.2.1.val v.2.2.val = m - 1) :
    evenRuleLocalRule m v c =
      axisOfLocalPerm
        (if v.1.val = half m - 1 ∨ v.1.val = half m
         then LocalPerm.p210
         else LocalPerm.p120) c := by
  unfold evenRuleLocalRule evenRuleAxis
  rw [evenRuleCode_of_eq_msub1
        m v.1.val v.2.1.val v.2.2.val hm hs]

theorem evenRuleLocalRule_cases
    (m : Nat) (v : VZ m) (hm : admissibleEvenM m) (c : Color) :
    (residualSupport m v.1.val v.2.1.val v.2.2.val = false ∧
      evenRuleLocalRule m v c = axisOfLocalPerm LocalPerm.p012 c) ∨
    (fiberSum m v.1.val v.2.1.val v.2.2.val = m - 2 ∧
      evenRuleLocalRule m v c =
        axisOfLocalPerm (tauLayerCode m v.1.val v.2.1.val) c) ∨
    (fiberSum m v.1.val v.2.1.val v.2.2.val = m - 1 ∧
      evenRuleLocalRule m v c =
        axisOfLocalPerm
          (if v.1.val = half m - 1 ∨ v.1.val = half m
           then LocalPerm.p210
           else LocalPerm.p120) c) := by
  by_cases hfalse : residualSupport m v.1.val v.2.1.val v.2.2.val = false
  · left
    constructor
    · exact hfalse
    · exact evenRuleLocalRule_of_not_residualSupport m v hm c hfalse
  · have hsupp : residualSupport m v.1.val v.2.1.val v.2.2.val = true := by
      cases hres : residualSupport m v.1.val v.2.1.val v.2.2.val <;> simp_all
    rcases evenRuleCode_on_residualSupport_cases
        m v.1.val v.2.1.val v.2.2.val hm hsupp with h2 | h1
    · right
      left
      constructor
      · exact h2.1
      · exact evenRuleLocalRule_of_eq_msub2 m v hm c h2.1
    · right
      right
      constructor
      · exact h1.1
      · exact evenRuleLocalRule_of_eq_msub1 m v hm c h1.1

end ClaudeCyclesARZN
