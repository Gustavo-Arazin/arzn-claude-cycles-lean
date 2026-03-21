import ClaudeCyclesARZN.EvenResidualSupport

namespace ClaudeCyclesARZN

/--
Residual normal-form shell for the canonical even rule.

This is intentionally a shell, not the final closure theorem:
it packages the three canonical branches of the rule into one
normal-form statement.

- outside the residual support: the rule is trivial (`012`);
- on `F_{m-2}`: the rule is exactly `tau(i,j)`;
- on `F_{m-1}`: the rule is the controlled splice branch.
-/
def canonicalEvenResidualNormalForm (m i j k : Nat) : Prop :=
  (residualSupport m i j k = false ∧
    evenRuleCode m i j k = LocalPerm.p012) ∨
  (fiberSum m i j k = m - 2 ∧
    evenRuleCode m i j k = tauLayerCode m i j) ∨
  (fiberSum m i j k = m - 1 ∧
    evenRuleCode m i j k =
      (if i = half m - 1 ∨ i = half m then LocalPerm.p210 else LocalPerm.p120))

/--
Global shell statement: every vertex is in canonical residual normal form.
-/
def HasCanonicalEvenResidualNormalForm (m : Nat) : Prop :=
  ∀ i j k, canonicalEvenResidualNormalForm m i j k

theorem canonicalEvenResidualNormalForm_of_not_residualSupport
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hfalse : residualSupport m i j k = false) :
    canonicalEvenResidualNormalForm m i j k := by
  left
  constructor
  · exact hfalse
  · exact evenRuleCode_of_not_residualSupport m i j k hm hfalse

theorem canonicalEvenResidualNormalForm_of_eq_msub2
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hs : fiberSum m i j k = m - 2) :
    canonicalEvenResidualNormalForm m i j k := by
  right
  left
  constructor
  · exact hs
  · exact evenRuleCode_of_eq_msub2 m i j k hm hs

theorem canonicalEvenResidualNormalForm_of_eq_msub1
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hs : fiberSum m i j k = m - 1) :
    canonicalEvenResidualNormalForm m i j k := by
  right
  right
  constructor
  · exact hs
  · exact evenRuleCode_of_eq_msub1 m i j k hm hs

/--
Master shell theorem: every point of the canonical even rule falls into one of the
three normal-form branches.
-/
theorem canonicalEvenResidualNormalForm_of_admissible
    (m i j k : Nat)
    (hm : admissibleEvenM m) :
    canonicalEvenResidualNormalForm m i j k := by
  by_cases hfalse : residualSupport m i j k = false
  · exact
      canonicalEvenResidualNormalForm_of_not_residualSupport
        m i j k hm hfalse
  · have hsupp : residualSupport m i j k = true := by
      cases hres : residualSupport m i j k <;> simp_all
    have hcases :=
      evenRuleCode_on_residualSupport_cases m i j k hm hsupp
    rcases hcases with h2 | h1
    · exact
        canonicalEvenResidualNormalForm_of_eq_msub2
          m i j k hm h2.1
    · exact
        canonicalEvenResidualNormalForm_of_eq_msub1
          m i j k hm h1.1

theorem hasCanonicalEvenResidualNormalForm
    (m : Nat)
    (hm : admissibleEvenM m) :
    HasCanonicalEvenResidualNormalForm m := by
  intro i j k
  exact canonicalEvenResidualNormalForm_of_admissible m i j k hm

/--
Any genuinely nontrivial branch of the canonical even rule must lie inside the
residual support.
-/
theorem nontrivial_evenRuleCode_implies_residualSupport
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hneq : evenRuleCode m i j k ≠ LocalPerm.p012) :
    residualSupport m i j k = true := by
  by_cases hfalse : residualSupport m i j k = false
  · have h012 : evenRuleCode m i j k = LocalPerm.p012 :=
      evenRuleCode_of_not_residualSupport m i j k hm hfalse
    exact False.elim (hneq h012)
  · cases hres : residualSupport m i j k <;> simp_all

/--
Prop-level version of the confinement statement:
nontriviality can only occur on the exceptional fibers.
-/
theorem nontrivial_evenRuleCode_implies_exceptionalFiberProp
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hneq : evenRuleCode m i j k ≠ LocalPerm.p012) :
    exceptionalFiberProp m i j k := by
  have hsupp : residualSupport m i j k = true :=
    nontrivial_evenRuleCode_implies_residualSupport m i j k hm hneq
  exact (residualSupportProp_iff_bool m i j k).2 hsupp

end ClaudeCyclesARZN
