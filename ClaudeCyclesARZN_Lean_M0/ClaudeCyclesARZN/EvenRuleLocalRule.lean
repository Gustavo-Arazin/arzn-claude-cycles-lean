import ClaudeCyclesARZN.EvenResidualNormalForm

namespace ClaudeCyclesARZN

/--
Interpret a local permutation code as the axis chosen by a given color.
The convention is:
- `0 ↦ x`
- `1 ↦ y`
- `2 ↦ z`
and the permutation code reorders these three axes.
-/
def axisOfLocalPerm (p : LocalPerm) (c : Color) : Axis :=
  match p, c.1 with
  | .p012, 0 => Axis.x
  | .p012, 1 => Axis.y
  | .p012, _ => Axis.z
  | .p021, 0 => Axis.x
  | .p021, 1 => Axis.z
  | .p021, _ => Axis.y
  | .p102, 0 => Axis.y
  | .p102, 1 => Axis.x
  | .p102, _ => Axis.z
  | .p120, 0 => Axis.y
  | .p120, 1 => Axis.z
  | .p120, _ => Axis.x
  | .p201, 0 => Axis.z
  | .p201, 1 => Axis.x
  | .p201, _ => Axis.y
  | .p210, 0 => Axis.z
  | .p210, 1 => Axis.y
  | .p210, _ => Axis.x

/-- Axis-level form of the canonical even rule at raw natural coordinates. -/
def evenRuleAxis (m i j k : Nat) (c : Color) : Axis :=
  axisOfLocalPerm (evenRuleCode m i j k) c

/--
Concrete `LocalRule` induced by the canonical even rule.

It reads the `ZMod m` coordinates of a vertex through their canonical representatives
in `{0, …, m-1}` and then applies `evenRuleCode`.
-/
def evenRuleLocalRule (m : Nat) : LocalRule m :=
  fun v c => evenRuleAxis m v.1.val v.2.1.val v.2.2.val c

@[simp] theorem evenRuleLocalRule_apply
    (m : Nat) (v : VZ m) (c : Color) :
    evenRuleLocalRule m v c =
      evenRuleAxis m v.1.val v.2.1.val v.2.2.val c := by
  rfl

@[simp] theorem evenRuleLocalRule_apply_tuple
    (m : Nat) (i j k : ZMod m) (c : Color) :
    evenRuleLocalRule m (i, j, k) c =
      evenRuleAxis m i.val j.val k.val c := by
  rfl

theorem evenRuleAxis_of_le_msub3
    (m i j k : Nat) (c : Color)
    (h : fiberSum m i j k ≤ m - 3) :
    evenRuleAxis m i j k c = axisOfLocalPerm LocalPerm.p012 c := by
  unfold evenRuleAxis
  rw [evenRuleCode_of_le_msub3 m i j k h]

theorem evenRuleAxis_of_not_residualSupport
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (c : Color)
    (hfalse : residualSupport m i j k = false) :
    evenRuleAxis m i j k c = axisOfLocalPerm LocalPerm.p012 c := by
  have hs : fiberSum m i j k ≤ m - 3 :=
    fiberSum_le_msub3_of_not_residualSupport m i j k hm hfalse
  exact evenRuleAxis_of_le_msub3 m i j k c hs

theorem evenRuleAxis_of_eq_msub2
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (c : Color)
    (hs : fiberSum m i j k = m - 2) :
    evenRuleAxis m i j k c = axisOfLocalPerm (tauLayerCode m i j) c := by
  unfold evenRuleAxis
  rw [evenRuleCode_of_eq_msub2 m i j k hm hs]

theorem evenRuleAxis_of_eq_msub1
    (m i j k : Nat)
    (hm : admissibleEvenM m)
    (c : Color)
    (hs : fiberSum m i j k = m - 1) :
    evenRuleAxis m i j k c =
      axisOfLocalPerm
        (if i = half m - 1 ∨ i = half m then LocalPerm.p210 else LocalPerm.p120) c := by
  unfold evenRuleAxis
  rw [evenRuleCode_of_eq_msub1 m i j k hm hs]

end ClaudeCyclesARZN
