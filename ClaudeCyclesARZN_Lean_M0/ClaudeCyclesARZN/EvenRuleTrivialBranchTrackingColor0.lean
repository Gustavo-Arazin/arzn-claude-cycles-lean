import ClaudeCyclesARZN.EvenRuleTrivialBranchTrackingArithmetic

namespace ClaudeCyclesARZN

/--
Named target for the color-0 arithmetic tracking problem on the trivial branch.
-/
def CanonicalEvenTrivialBranchTrackingColor0Target (m : Nat) : Prop :=
  ∀ z : VZ m,
    vertexFiberSum m z ≤ m - 3 →
    trivialBranchPrefixFiberTrackingColor0ArithmeticAt m z

theorem canonicalEvenTrivialBranchTrackingColor0At_of_target
    (m : Nat)
    (h0 : CanonicalEvenTrivialBranchTrackingColor0Target m)
    (z : VZ m)
    (hz : vertexFiberSum m z ≤ m - 3) :
    trivialBranchPrefixFiberTrackingColor0At m z := by
  exact trivialBranchPrefixFiberTrackingColor0At_of_arithmetic m z (h0 z hz)

theorem canonicalEvenTrivialBranchTrackingArithmeticColorCases_of_separateTargets
    (m : Nat)
    (h0 : CanonicalEvenTrivialBranchTrackingColor0Target m)
    (h1 :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchPrefixFiberTrackingColor1ArithmeticAt m z)
    (h2 :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchPrefixFiberTrackingColor2ArithmeticAt m z) :
    CanonicalEvenTrivialBranchTrackingArithmeticColorCases m := by
  intro z hz
  exact ⟨h0 z hz, h1 z hz, h2 z hz⟩

theorem canonicalEvenTrivialBranchTrackingColorCases_of_separateTargets
    (m : Nat)
    (h0 : CanonicalEvenTrivialBranchTrackingColor0Target m)
    (h1 :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchPrefixFiberTrackingColor1ArithmeticAt m z)
    (h2 :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchPrefixFiberTrackingColor2ArithmeticAt m z) :
    CanonicalEvenTrivialBranchTrackingColorCases m := by
  apply canonicalEvenTrivialBranchTrackingColorCases_of_arithmetic
  exact
    canonicalEvenTrivialBranchTrackingArithmeticColorCases_of_separateTargets
      m h0 h1 h2

end ClaudeCyclesARZN
