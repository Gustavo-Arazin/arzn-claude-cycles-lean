import ClaudeCyclesARZN.EvenRuleTrivialBranchTrackingArithmetic

namespace ClaudeCyclesARZN

theorem trivialBranchPrefixFiberTrackingColor0Arithmetic_all
    (m : Nat) (hm : admissibleEvenM m) (z : VZ m) :
    trivialBranchPrefixFiberTrackingColor0ArithmeticAt m z := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  rcases z with ⟨i, j, k⟩
  intro t ht
  have htm : t < m := by
    exact Nat.lt_trans ht (by simpa [fiberIndex] using (ZMod.val_lt (i + j + k : ZMod m)))
  have hEqNatCast :
      ((fiberSum m (i - (i + j + k) + (t : ZMod m)).val j.val k.val : Nat) : ZMod m) = (t : ZMod m) := by
    calc
      ((fiberSum m (i - (i + j + k) + (t : ZMod m)).val j.val k.val : Nat) : ZMod m)
          =
      ((((i - (i + j + k) + (t : ZMod m)).val + j.val + k.val : Nat)) : ZMod m) := by
            simp [fiberSum]
      _ =
      ((((i - (i + j + k) + (t : ZMod m)).val : Nat) : ZMod m) +
        ((j.val : Nat) : ZMod m) +
        ((k.val : Nat) : ZMod m)) := by
            simp [Nat.cast_add, add_assoc]
      _ = i - (i + j + k) + (t : ZMod m) + j + k := by
            rw [ZMod.natCast_zmod_val (i - (i + j + k) + (t : ZMod m)),
                ZMod.natCast_zmod_val j,
                ZMod.natCast_zmod_val k]
      _ = (t : ZMod m) := by
            ring
  have hleftlt : fiberSum m (i - (i + j + k) + (t : ZMod m)).val j.val k.val < m := by
    unfold fiberSum
    exact Nat.mod_lt _ (by omega)
  have hvals :
      ((fiberSum m (i - (i + j + k) + (t : ZMod m)).val j.val k.val : Nat) : ZMod m).val
      = ((t : ZMod m)).val := by
    exact congrArg ZMod.val hEqNatCast
  rw [ZMod.val_natCast_of_lt hleftlt, ZMod.val_natCast_of_lt htm] at hvals
  exact hvals

theorem trivialBranchPrefixFiberTrackingColor1Arithmetic_all
    (m : Nat) (hm : admissibleEvenM m) (z : VZ m) :
    trivialBranchPrefixFiberTrackingColor1ArithmeticAt m z := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  rcases z with ⟨i, j, k⟩
  intro t ht
  have htm : t < m := by
    exact Nat.lt_trans ht (by simpa [fiberIndex] using (ZMod.val_lt (i + j + k : ZMod m)))
  have hEqNatCast :
      ((fiberSum m i.val (j - (i + j + k) + (t : ZMod m)).val k.val : Nat) : ZMod m) = (t : ZMod m) := by
    calc
      ((fiberSum m i.val (j - (i + j + k) + (t : ZMod m)).val k.val : Nat) : ZMod m)
          =
      (((i.val + (j - (i + j + k) + (t : ZMod m)).val + k.val : Nat)) : ZMod m) := by
            simp [fiberSum]
      _ =
      (((i.val : Nat) : ZMod m) +
        (((j - (i + j + k) + (t : ZMod m)).val : Nat) : ZMod m) +
        ((k.val : Nat) : ZMod m)) := by
            simp [Nat.cast_add, add_assoc]
      _ = i + (j - (i + j + k) + (t : ZMod m)) + k := by
            rw [ZMod.natCast_zmod_val i,
                ZMod.natCast_zmod_val (j - (i + j + k) + (t : ZMod m)),
                ZMod.natCast_zmod_val k]
      _ = (t : ZMod m) := by
            ring
  have hleftlt : fiberSum m i.val (j - (i + j + k) + (t : ZMod m)).val k.val < m := by
    unfold fiberSum
    exact Nat.mod_lt _ (by omega)
  have hvals :
      ((fiberSum m i.val (j - (i + j + k) + (t : ZMod m)).val k.val : Nat) : ZMod m).val
      = ((t : ZMod m)).val := by
    exact congrArg ZMod.val hEqNatCast
  rw [ZMod.val_natCast_of_lt hleftlt, ZMod.val_natCast_of_lt htm] at hvals
  exact hvals

theorem trivialBranchPrefixFiberTrackingColor2Arithmetic_all
    (m : Nat) (hm : admissibleEvenM m) (z : VZ m) :
    trivialBranchPrefixFiberTrackingColor2ArithmeticAt m z := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  rcases z with ⟨i, j, k⟩
  intro t ht
  have htm : t < m := by
    exact Nat.lt_trans ht (by simpa [fiberIndex] using (ZMod.val_lt (i + j + k : ZMod m)))
  have hEqNatCast :
      ((fiberSum m i.val j.val (k - (i + j + k) + (t : ZMod m)).val : Nat) : ZMod m) = (t : ZMod m) := by
    calc
      ((fiberSum m i.val j.val (k - (i + j + k) + (t : ZMod m)).val : Nat) : ZMod m)
          =
      (((i.val + j.val + (k - (i + j + k) + (t : ZMod m)).val : Nat)) : ZMod m) := by
            simp [fiberSum]
      _ =
      (((i.val : Nat) : ZMod m) +
        ((j.val : Nat) : ZMod m) +
        (((k - (i + j + k) + (t : ZMod m)).val : Nat) : ZMod m)) := by
            simp [Nat.cast_add, add_assoc]
      _ = i + j + (k - (i + j + k) + (t : ZMod m)) := by
            rw [ZMod.natCast_zmod_val i,
                ZMod.natCast_zmod_val j,
                ZMod.natCast_zmod_val (k - (i + j + k) + (t : ZMod m))]
      _ = (t : ZMod m) := by
            ring
  have hleftlt : fiberSum m i.val j.val (k - (i + j + k) + (t : ZMod m)).val < m := by
    unfold fiberSum
    exact Nat.mod_lt _ (by omega)
  have hvals :
      ((fiberSum m i.val j.val (k - (i + j + k) + (t : ZMod m)).val : Nat) : ZMod m).val
      = ((t : ZMod m)).val := by
    exact congrArg ZMod.val hEqNatCast
  rw [ZMod.val_natCast_of_lt hleftlt, ZMod.val_natCast_of_lt htm] at hvals
  exact hvals

theorem canonicalEvenTrivialBranchTrackingArithmeticColorCases_all
    (m : Nat) (hm : admissibleEvenM m) :
    CanonicalEvenTrivialBranchTrackingArithmeticColorCases m := by
  intro z hz
  constructor
  · exact trivialBranchPrefixFiberTrackingColor0Arithmetic_all m hm z
  · constructor
    · exact trivialBranchPrefixFiberTrackingColor1Arithmetic_all m hm z
    · exact trivialBranchPrefixFiberTrackingColor2Arithmetic_all m hm z

theorem canonicalEvenTrivialBranchTrackingColorCases_all
    (m : Nat) (hm : admissibleEvenM m) :
    CanonicalEvenTrivialBranchTrackingColorCases m := by
  apply canonicalEvenTrivialBranchTrackingColorCases_of_arithmetic
  exact canonicalEvenTrivialBranchTrackingArithmeticColorCases_all m hm

end ClaudeCyclesARZN
