import ClaudeCyclesARZN.Torus
import ClaudeCyclesARZN.EvenResidualNormalForm

namespace ClaudeCyclesARZN

/--
Interpret a local permutation code as the axis chosen by a given color.

Convention:
- color 0 reads the first position of the permutation;
- color 1 reads the second position;
- color 2 reads the third position.
-/
def axisOfLocalPerm (p : LocalPerm) (c : Color) : Axis :=
  match p, c.val with
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

It reads the `ZMod m` coordinates of a vertex via their canonical representatives
in `{0, ..., m-1}` and then applies `evenRuleCode`.
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

end ClaudeCyclesARZN
