import ClaudeCyclesARZN.EvenRuleTrivialBranchTrackingColor0

namespace ClaudeCyclesARZN

/--
Exact modular core still needed to prove the color-0 tracking target.

This isolates the remaining difficulty in its cleanest form:
the nat-level tracking statement will follow once this equality in `ZMod m`
is available pointwise.
-/
def CanonicalEvenTrivialBranchTrackingColor0ModCore (m : Nat) : Prop :=
  ∀ z : VZ m, ∀ t : Nat,
    t < (fiberIndex z).val →
    ((fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val : Nat) : ZMod m)
      = (t : ZMod m)

theorem canonicalEvenTrivialBranchTrackingColor0Target_of_modCore
    (m : Nat) (hm : admissibleEvenM m)
    (hcore : CanonicalEvenTrivialBranchTrackingColor0ModCore m) :
    CanonicalEvenTrivialBranchTrackingColor0Target m := by
  intro z hz t ht
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  have hmpos : 0 < m := by
    rcases hm with ⟨hm8, _⟩
    omega
  have hmod :
      ((fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val : Nat) : ZMod m)
        = (t : ZMod m) := by
    exact hcore z t ht
  have hleftlt :
      fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val < m := by
    unfold fiberSum
    exact Nat.mod_lt _ hmpos
  have hfiblt : (fiberIndex z).val < m := by
    simpa using (ZMod.val_lt (fiberIndex z))
  have htm : t < m := Nat.lt_trans ht hfiblt
  have hvals :
      (((fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val : Nat) : ZMod m)).val
        = ((t : ZMod m)).val := by
    exact congrArg ZMod.val hmod
  have hleftval :
      (((fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val : Nat) : ZMod m)).val
        =
      fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val := by
    exact ZMod.val_natCast_of_lt hleftlt
  have htval : ((t : ZMod m)).val = t := by
    exact ZMod.val_natCast_of_lt htm
  rw [hleftval, htval] at hvals
  exact hvals

theorem canonicalEvenTrivialBranchTrackingColor0ModCore_all
    (m : Nat) (hm : admissibleEvenM m) :
    CanonicalEvenTrivialBranchTrackingColor0ModCore m := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  intro z t ht
  rcases z with ⟨i, j, k⟩
  unfold fiberSum
  have hcastmod :
      (((((i - (i + j + k) + (t : ZMod m)).val + j.val + k.val) % m : Nat) : ZMod m))
        =
      ((((i - (i + j + k) + (t : ZMod m)).val + j.val + k.val : Nat)) : ZMod m) := by
    simp
  rw [hcastmod]
  rw [← ZMod.natCast_zmod_val (i - (i + j + k) + (t : ZMod m))]
  rw [← ZMod.natCast_zmod_val j]
  rw [← ZMod.natCast_zmod_val k]
  change i - (i + j + k) + (t : ZMod m) + j + k = (t : ZMod m)
  ring

theorem canonicalEvenTrivialBranchTrackingColor0Target_all
    (m : Nat) (hm : admissibleEvenM m) :
    CanonicalEvenTrivialBranchTrackingColor0Target m := by
  exact canonicalEvenTrivialBranchTrackingColor0Target_of_modCore
    m hm
    (canonicalEvenTrivialBranchTrackingColor0ModCore_all m hm)

theorem canonicalEvenTrivialBranchTrackingColorCases_of_modCoreColor0
    (m : Nat) (hm : admissibleEvenM m)
    (h0 : CanonicalEvenTrivialBranchTrackingColor0ModCore m)
    (h1 :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchPrefixFiberTrackingColor1ArithmeticAt m z)
    (h2 :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchPrefixFiberTrackingColor2ArithmeticAt m z) :
    CanonicalEvenTrivialBranchTrackingColorCases m := by
  apply canonicalEvenTrivialBranchTrackingColorCases_of_separateTargets
  · exact canonicalEvenTrivialBranchTrackingColor0Target_of_modCore m hm h0
  · exact h1
  · exact h2

end ClaudeCyclesARZN
