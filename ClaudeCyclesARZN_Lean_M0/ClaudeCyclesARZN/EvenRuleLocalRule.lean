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

@[simp] theorem axisOfLocalPerm_p012_color0 :
    axisOfLocalPerm LocalPerm.p012 (0 : Color) = Axis.x := rfl
@[simp] theorem axisOfLocalPerm_p012_color1 :
    axisOfLocalPerm LocalPerm.p012 (1 : Color) = Axis.y := rfl
@[simp] theorem axisOfLocalPerm_p012_color2 :
    axisOfLocalPerm LocalPerm.p012 (2 : Color) = Axis.z := rfl

@[simp] theorem axisOfLocalPerm_p021_color0 :
    axisOfLocalPerm LocalPerm.p021 (0 : Color) = Axis.x := rfl
@[simp] theorem axisOfLocalPerm_p021_color1 :
    axisOfLocalPerm LocalPerm.p021 (1 : Color) = Axis.z := rfl
@[simp] theorem axisOfLocalPerm_p021_color2 :
    axisOfLocalPerm LocalPerm.p021 (2 : Color) = Axis.y := rfl

@[simp] theorem axisOfLocalPerm_p102_color0 :
    axisOfLocalPerm LocalPerm.p102 (0 : Color) = Axis.y := rfl
@[simp] theorem axisOfLocalPerm_p102_color1 :
    axisOfLocalPerm LocalPerm.p102 (1 : Color) = Axis.x := rfl
@[simp] theorem axisOfLocalPerm_p102_color2 :
    axisOfLocalPerm LocalPerm.p102 (2 : Color) = Axis.z := rfl

@[simp] theorem axisOfLocalPerm_p120_color0 :
    axisOfLocalPerm LocalPerm.p120 (0 : Color) = Axis.y := rfl
@[simp] theorem axisOfLocalPerm_p120_color1 :
    axisOfLocalPerm LocalPerm.p120 (1 : Color) = Axis.z := rfl
@[simp] theorem axisOfLocalPerm_p120_color2 :
    axisOfLocalPerm LocalPerm.p120 (2 : Color) = Axis.x := rfl

@[simp] theorem axisOfLocalPerm_p201_color0 :
    axisOfLocalPerm LocalPerm.p201 (0 : Color) = Axis.z := rfl
@[simp] theorem axisOfLocalPerm_p201_color1 :
    axisOfLocalPerm LocalPerm.p201 (1 : Color) = Axis.x := rfl
@[simp] theorem axisOfLocalPerm_p201_color2 :
    axisOfLocalPerm LocalPerm.p201 (2 : Color) = Axis.y := rfl

@[simp] theorem axisOfLocalPerm_p210_color0 :
    axisOfLocalPerm LocalPerm.p210 (0 : Color) = Axis.z := rfl
@[simp] theorem axisOfLocalPerm_p210_color1 :
    axisOfLocalPerm LocalPerm.p210 (1 : Color) = Axis.y := rfl
@[simp] theorem axisOfLocalPerm_p210_color2 :
    axisOfLocalPerm LocalPerm.p210 (2 : Color) = Axis.x := rfl

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
