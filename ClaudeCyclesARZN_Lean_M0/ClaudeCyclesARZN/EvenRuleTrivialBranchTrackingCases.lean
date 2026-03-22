import ClaudeCyclesARZN.EvenRuleTrivialBranchArithmeticTargets

namespace ClaudeCyclesARZN

/--
Color-0 version of the trivial-branch tracking target.
-/
def trivialBranchPrefixFiberTrackingColor0At
    (m : Nat) (z : VZ m) : Prop :=
  ∀ t : Nat,
    t < (fiberIndex z).val →
    let v := succPow (pure012LocalRule m) (0 : Color) t
      (canonicalEvenWitnessCandidate m (0 : Color) z).1
    fiberSum m v.1.val v.2.1.val v.2.2.val = t

/--
Color-1 version of the trivial-branch tracking target.
-/
def trivialBranchPrefixFiberTrackingColor1At
    (m : Nat) (z : VZ m) : Prop :=
  ∀ t : Nat,
    t < (fiberIndex z).val →
    let v := succPow (pure012LocalRule m) (1 : Color) t
      (canonicalEvenWitnessCandidate m (1 : Color) z).1
    fiberSum m v.1.val v.2.1.val v.2.2.val = t

/--
Color-2 version of the trivial-branch tracking target.
-/
def trivialBranchPrefixFiberTrackingColor2At
    (m : Nat) (z : VZ m) : Prop :=
  ∀ t : Nat,
    t < (fiberIndex z).val →
    let v := succPow (pure012LocalRule m) (2 : Color) t
      (canonicalEvenWitnessCandidate m (2 : Color) z).1
    fiberSum m v.1.val v.2.1.val v.2.2.val = t

/--
Recombine the three colorwise tracking obligations into the generic
trivial-branch tracking target.
-/
theorem trivialBranchPrefixFiberTrackingAt_of_colorCases
    (m : Nat) (c : Color) (z : VZ m)
    (h0 : trivialBranchPrefixFiberTrackingColor0At m z)
    (h1 : trivialBranchPrefixFiberTrackingColor1At m z)
    (h2 : trivialBranchPrefixFiberTrackingColor2At m z) :
    trivialBranchPrefixFiberTrackingAt m c z := by
  fin_cases c
  · simpa [trivialBranchPrefixFiberTrackingAt, trivialBranchPrefixFiberTrackingColor0At] using h0
  · simpa [trivialBranchPrefixFiberTrackingAt, trivialBranchPrefixFiberTrackingColor1At] using h1
  · simpa [trivialBranchPrefixFiberTrackingAt, trivialBranchPrefixFiberTrackingColor2At] using h2

/--
Packaged remaining tracking target for the trivial region:
for each trivial target `z`, it is enough to prove the three colorwise tracking facts.
-/
def CanonicalEvenTrivialBranchTrackingColorCases (m : Nat) : Prop :=
  ∀ z : VZ m,
    vertexFiberSum m z ≤ m - 3 →
    trivialBranchPrefixFiberTrackingColor0At m z ∧
    trivialBranchPrefixFiberTrackingColor1At m z ∧
    trivialBranchPrefixFiberTrackingColor2At m z

/--
Reduce the full trivial-branch arithmetic target to:
- a bound helper;
- the three colorwise tracking cases.
-/
theorem canonicalEvenTrivialBranchArithmeticTargets_of_bound_and_colorCases
    (m : Nat)
    (hbound :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchTargetBoundAt m z)
    (htrack :
      CanonicalEvenTrivialBranchTrackingColorCases m) :
    CanonicalEvenTrivialBranchArithmeticTargets m := by
  intro c z hz
  rcases htrack z hz with ⟨h0, h1, h2⟩
  constructor
  · exact hbound z hz
  · exact trivialBranchPrefixFiberTrackingAt_of_colorCases m c z h0 h1 h2

end ClaudeCyclesARZN
