import ClaudeCyclesARZN.EvenRuleWitnessCandidates

namespace ClaudeCyclesARZN

/--
The constant local rule corresponding to the permutation code `012`.
-/
def pure012LocalRule (m : Nat) : LocalRule m :=
  fun _ c => axisOfLocalPerm LocalPerm.p012 c

@[simp] theorem pure012LocalRule_apply
    (m : Nat) (v : VZ m) (c : Color) :
    pure012LocalRule m v c = axisOfLocalPerm LocalPerm.p012 c := by
  rfl

@[simp] theorem succ_pure012_color0
    (m : Nat) (v : VZ m) :
    succ (pure012LocalRule m) (0 : Color) v = bumpX v := by
  rcases v with ⟨i, j, k⟩
  simp [succ, pure012LocalRule, axisOfLocalPerm, bump, bumpX]

@[simp] theorem succ_pure012_color1
    (m : Nat) (v : VZ m) :
    succ (pure012LocalRule m) (1 : Color) v = bumpY v := by
  rcases v with ⟨i, j, k⟩
  simp [succ, pure012LocalRule, axisOfLocalPerm, bump, bumpY]

@[simp] theorem succ_pure012_color2
    (m : Nat) (v : VZ m) :
    succ (pure012LocalRule m) (2 : Color) v = bumpZ v := by
  rcases v with ⟨i, j, k⟩
  simp [succ, pure012LocalRule, axisOfLocalPerm, bump, bumpZ]

@[simp] theorem succPow_pure012_color0
    (m : Nat) (n : Nat) (i j k : ZMod m) :
    succPow (pure012LocalRule m) (0 : Color) n (i, j, k) = (i + n, j, k) := by
  induction n generalizing i with
  | zero =>
      simp [succPow]
  | succ n ih =>
      rw [succPow_succ, succ_pure012_color0, ih]
      ext <;> simp [bumpX, bump, Nat.cast_add, add_assoc]

@[simp] theorem succPow_pure012_color1
    (m : Nat) (n : Nat) (i j k : ZMod m) :
    succPow (pure012LocalRule m) (1 : Color) n (i, j, k) = (i, j + n, k) := by
  induction n generalizing j with
  | zero =>
      simp [succPow]
  | succ n ih =>
      rw [succPow_succ, succ_pure012_color1, ih]
      ext <;> simp [bumpY, bump, Nat.cast_add, add_assoc]

@[simp] theorem succPow_pure012_color2
    (m : Nat) (n : Nat) (i j k : ZMod m) :
    succPow (pure012LocalRule m) (2 : Color) n (i, j, k) = (i, j, k + n) := by
  induction n generalizing k with
  | zero =>
      simp [succPow]
  | succ n ih =>
      rw [succPow_succ, succ_pure012_color2, ih]
      ext <;> simp [bumpZ, bump, Nat.cast_add, add_assoc]

end ClaudeCyclesARZN
