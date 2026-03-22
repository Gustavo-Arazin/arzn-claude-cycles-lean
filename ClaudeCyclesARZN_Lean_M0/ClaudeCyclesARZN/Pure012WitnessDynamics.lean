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
      simp [succPow, ih, Nat.cast_add, add_assoc]

@[simp] theorem succPow_pure012_color1
    (m : Nat) (n : Nat) (i j k : ZMod m) :
    succPow (pure012LocalRule m) (1 : Color) n (i, j, k) = (i, j + n, k) := by
  induction n generalizing j with
  | zero =>
      simp [succPow]
  | succ n ih =>
      simp [succPow, ih, Nat.cast_add, add_assoc]

@[simp] theorem succPow_pure012_color2
    (m : Nat) (n : Nat) (i j k : ZMod m) :
    succPow (pure012LocalRule m) (2 : Color) n (i, j, k) = (i, j, k + n) := by
  induction n generalizing k with
  | zero =>
      simp [succPow]
  | succ n ih =>
      simp [succPow, ih, Nat.cast_add, add_assoc]

theorem canonicalEvenCandidateHits_pure012_color0
    (m : Nat) (z : VZ m) :
    (residualMapFromFiberZero
        (pure012LocalRule m) (0 : Color) (fiberIndex z).val
        (canonicalEvenWitnessCandidate m (0 : Color) z)).1 = z := by
  rcases z with ⟨i, j, k⟩
  rw [residualMapFromFiberZero_val]
  ext <;> simp [canonicalEvenWitnessCandidate, fiberIndex]
  · calc
      i - (i + j + k) + (((i + j + k).val : Nat) : ZMod m)
          = i - (i + j + k) + (i + j + k) := by
              rw [ZMod.natCast_zmod_val]
      _ = i := by ring

theorem canonicalEvenCandidateHits_pure012_color1
    (m : Nat) (z : VZ m) :
    (residualMapFromFiberZero
        (pure012LocalRule m) (1 : Color) (fiberIndex z).val
        (canonicalEvenWitnessCandidate m (1 : Color) z)).1 = z := by
  rcases z with ⟨i, j, k⟩
  rw [residualMapFromFiberZero_val]
  ext <;> simp [canonicalEvenWitnessCandidate, fiberIndex]
  · calc
      j - (i + j + k) + (((i + j + k).val : Nat) : ZMod m)
          = j - (i + j + k) + (i + j + k) := by
              rw [ZMod.natCast_zmod_val]
      _ = j := by ring

theorem canonicalEvenCandidateHits_pure012_color2
    (m : Nat) (z : VZ m) :
    (residualMapFromFiberZero
        (pure012LocalRule m) (2 : Color) (fiberIndex z).val
        (canonicalEvenWitnessCandidate m (2 : Color) z)).1 = z := by
  rcases z with ⟨i, j, k⟩
  rw [residualMapFromFiberZero_val]
  ext <;> simp [canonicalEvenWitnessCandidate, fiberIndex]
  · calc
      k - (i + j + k) + (((i + j + k).val : Nat) : ZMod m)
          = k - (i + j + k) + (i + j + k) := by
              rw [ZMod.natCast_zmod_val]
      _ = k := by ring

theorem canonicalEvenCandidateHits_pure012
    (m : Nat) (c : Color) (z : VZ m) :
    (residualMapFromFiberZero
        (pure012LocalRule m) c (fiberIndex z).val
        (canonicalEvenWitnessCandidate m c z)).1 = z := by
  fin_cases c
  · simpa using canonicalEvenCandidateHits_pure012_color0 m z
  · simpa using canonicalEvenCandidateHits_pure012_color1 m z
  · simpa using canonicalEvenCandidateHits_pure012_color2 m z

end ClaudeCyclesARZN
