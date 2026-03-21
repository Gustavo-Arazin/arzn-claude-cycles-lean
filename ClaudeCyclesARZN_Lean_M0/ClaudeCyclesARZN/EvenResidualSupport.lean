import ClaudeCyclesARZN.EvenExceptionalFibers

namespace ClaudeCyclesARZN

/--
Residual support for the canonical even rule.

At this checkpoint, the residual support is exactly the union of the two
exceptional fibers `F_{m-2}` and `F_{m-1}`.
-/
def residualSupport (m i j k : Nat) : Bool :=
  isExceptionalFiber m (fiberSum m i j k)

/--
Prop-level version of `residualSupport`.
-/
def residualSupportProp (m i j k : Nat) : Prop :=
  exceptionalFiberProp m i j k

theorem residualSupport_eq_exceptionalFiber
    (m i j k : Nat) :
    residualSupport m i j k = isExceptionalFiber m (fiberSum m i j k) := by
  rfl

theorem residualSupportProp_eq_exceptionalFiberProp
    (m i j k : Nat) :
    residualSupportProp m i j k ↔ exceptionalFiberProp m i j k := by
  rfl

theorem residualSupportProp_iff_bool
    (m i j k : Nat) :
    residualSupportProp m i j k ↔ residualSupport m i j k = true := by
  unfold residualSupportProp residualSupport
  exact exceptionalFiberProp_iff_bool m i j k

theorem residualSupport_eq_true_iff
    (m i j k : Nat) :
    residualSupport m i j k = true ↔
      fiberSum m i j k = m - 2 ∨ fiberSum m i j k = m - 1 := by
  unfold residualSupport
  exact isExceptionalFiber_eq_true_iff m (fiberSum m i j k)

theorem residualSupport_eq_false_iff
    (m i j k : Nat) :
    residualSupport m i j k = false ↔
      fiberSum m i j k ≠ m - 2 ∧ fiberSum m i j k ≠ m - 1 := by
  unfold residualSupport
  exact isExceptionalFiber_eq_false_iff m (fiberSum m i j k)

theorem residualSupport_of_eq_msub2
    (m i j k : Nat)
    (hs : fiberSum m i j k = m - 2) :
    residualSupport m i j k = true := by
  unfold residualSupport
  exact isExceptionalFiber_of_eq_msub2 m (fiberSum m i j k) hs

theorem residualSupport_of_eq_msub1
    (m i j k : Nat)
    (hs : fiberSum m i j k = m - 1) :
    residualSupport m i j k = true := by
  unfold residualSupport
  exact isExceptionalFiber_of_eq_msub1 m (fiberSum m i j k) hs

theorem not_residualSupport_of_le_msub3
    (m i j k : Nat)
    (hm : 8 ≤ m)
    (hs : fiberSum m i j k ≤ m - 3) :
    residualSupport m i j k = false := by
  unfold residualSupport
  exact not_exceptional_of_le_msub3 m (fiberSum m i j k) hm hs

theorem fiberSum_le_msub3_of_not_residualSupport
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hfalse : residualSupport m i j k = false) :
    fiberSum m i j k ≤ m - 3 := by
  apply fiberSum_le_msub3_of_not_exceptional m i j k hm
  simpa [residualSupport] using hfalse

/--
Outside the residual support, the canonical even rule is trivial: it is `012`.
-/
theorem evenRuleCode_of_not_residualSupport
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hfalse : residualSupport m i j k = false) :
    evenRuleCode m i j k = LocalPerm.p012 := by
  apply evenRuleCode_of_not_exceptional m i j k hm
  simpa [residualSupport] using hfalse

/--
On the fiber `F_{m-2}`, the rule is exactly the frozen table `tau(i,j)`.
-/
theorem evenRuleCode_on_residualSupport_of_eq_msub2
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hs : fiberSum m i j k = m - 2) :
    residualSupport m i j k = true ∧
    evenRuleCode m i j k = tauLayerCode m i j := by
  constructor
  · exact residualSupport_of_eq_msub2 m i j k hs
  · exact evenRuleCode_of_eq_msub2 m i j k hm hs

/--
On the fiber `F_{m-1}`, the rule is the controlled splice behavior:
`210` on the two central `i`-columns and `120` otherwise.
-/
theorem evenRuleCode_on_residualSupport_of_eq_msub1
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hs : fiberSum m i j k = m - 1) :
    residualSupport m i j k = true ∧
    evenRuleCode m i j k =
      (if i = half m - 1 ∨ i = half m then LocalPerm.p210 else LocalPerm.p120) := by
  constructor
  · exact residualSupport_of_eq_msub1 m i j k hs
  · exact evenRuleCode_of_eq_msub1 m i j k hm hs

/--
Master case split for the residual support shell:
if a vertex lies in residual support, then its fiber is one of the two exceptional
ones, and the rule is completely controlled by the corresponding branch.
-/
theorem evenRuleCode_on_residualSupport_cases
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (hsupp : residualSupport m i j k = true) :
    (fiberSum m i j k = m - 2 ∧
      evenRuleCode m i j k = tauLayerCode m i j) ∨
    (fiberSum m i j k = m - 1 ∧
      evenRuleCode m i j k =
        (if i = half m - 1 ∨ i = half m then LocalPerm.p210 else LocalPerm.p120)) := by
  have hs :
      fiberSum m i j k = m - 2 ∨ fiberSum m i j k = m - 1 := by
    exact (residualSupport_eq_true_iff m i j k).mp hsupp
  rcases hs with hs2 | hs1
  · left
    constructor
    · exact hs2
    · exact evenRuleCode_of_eq_msub2 m i j k hm hs2
  · right
    constructor
    · exact hs1
    · exact evenRuleCode_of_eq_msub1 m i j k hm hs1

end ClaudeCyclesARZN
