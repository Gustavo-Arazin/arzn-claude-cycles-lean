import ClaudeCyclesARZN.EvenRuleLocalRuleFacts

namespace ClaudeCyclesARZN

/--
LocalRule-side residual normal form for the canonical even rule.

This is the `VZ m × Color` version of the M3 shell:
- outside residual support, the rule is `012`;
- on `F_{m-2}`, the rule is `tau(i,j)`;
- on `F_{m-1}`, the rule is the controlled splice branch.
-/
def canonicalEvenLocalResidualNormalForm
    (m : Nat) (v : VZ m) (c : Color) : Prop :=
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
         else LocalPerm.p120) c)

/--
Packaged version: the canonical even rule is in local residual normal form
at every vertex and for every color.
-/
def HasCanonicalEvenLocalResidualNormalForm (m : Nat) : Prop :=
  ∀ v : VZ m, ∀ c : Color, canonicalEvenLocalResidualNormalForm m v c

theorem canonicalEvenLocalResidualNormalForm_of_not_residualSupport
    (m : Nat) (v : VZ m) (hm : admissibleEvenM m) (c : Color)
    (hfalse : residualSupport m v.1.val v.2.1.val v.2.2.val = false) :
    canonicalEvenLocalResidualNormalForm m v c := by
  unfold canonicalEvenLocalResidualNormalForm
  left
  constructor
  · exact hfalse
  · exact evenRuleLocalRule_of_not_residualSupport m v hm c hfalse

theorem canonicalEvenLocalResidualNormalForm_of_eq_msub2
    (m : Nat) (v : VZ m) (hm : admissibleEvenM m) (c : Color)
    (hs : fiberSum m v.1.val v.2.1.val v.2.2.val = m - 2) :
    canonicalEvenLocalResidualNormalForm m v c := by
  unfold canonicalEvenLocalResidualNormalForm
  right
  left
  constructor
  · exact hs
  · exact evenRuleLocalRule_of_eq_msub2 m v hm c hs

theorem canonicalEvenLocalResidualNormalForm_of_eq_msub1
    (m : Nat) (v : VZ m) (hm : admissibleEvenM m) (c : Color)
    (hs : fiberSum m v.1.val v.2.1.val v.2.2.val = m - 1) :
    canonicalEvenLocalResidualNormalForm m v c := by
  unfold canonicalEvenLocalResidualNormalForm
  right
  right
  constructor
  · exact hs
  · exact evenRuleLocalRule_of_eq_msub1 m v hm c hs

theorem canonicalEvenLocalResidualNormalForm_of_admissible
    (m : Nat) (v : VZ m) (hm : admissibleEvenM m) (c : Color) :
    canonicalEvenLocalResidualNormalForm m v c := by
  unfold canonicalEvenLocalResidualNormalForm
  exact evenRuleLocalRule_cases m v hm c

theorem hasCanonicalEvenLocalResidualNormalForm
    (m : Nat) (hm : admissibleEvenM m) :
    HasCanonicalEvenLocalResidualNormalForm m := by
  intro v c
  exact canonicalEvenLocalResidualNormalForm_of_admissible m v hm c

end ClaudeCyclesARZN
