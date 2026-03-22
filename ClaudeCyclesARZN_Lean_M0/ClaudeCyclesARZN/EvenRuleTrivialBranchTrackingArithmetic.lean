import ClaudeCyclesARZN.EvenRuleTrivialBranchTrackingCases

namespace ClaudeCyclesARZN

theorem pure012_candidate_orbit_color0
    (m : Nat) (z : VZ m) (t : Nat) :
    succPow (pure012LocalRule m) (0 : Color) t
      (canonicalEvenWitnessCandidate m (0 : Color) z).1
      =
    (z.1 - fiberIndex z + t, z.2.1, z.2.2) := by
  rcases z with ⟨i, j, k⟩
  simp [canonicalEvenWitnessCandidate, fiberIndex, succPow_pure012_color0, add_assoc]

theorem pure012_candidate_orbit_color1
    (m : Nat) (z : VZ m) (t : Nat) :
    succPow (pure012LocalRule m) (1 : Color) t
      (canonicalEvenWitnessCandidate m (1 : Color) z).1
      =
    (z.1, z.2.1 - fiberIndex z + t, z.2.2) := by
  rcases z with ⟨i, j, k⟩
  simp [canonicalEvenWitnessCandidate, fiberIndex, succPow_pure012_color1, add_assoc]

theorem pure012_candidate_orbit_color2
    (m : Nat) (z : VZ m) (t : Nat) :
    succPow (pure012LocalRule m) (2 : Color) t
      (canonicalEvenWitnessCandidate m (2 : Color) z).1
      =
    (z.1, z.2.1, z.2.2 - fiberIndex z + t) := by
  rcases z with ⟨i, j, k⟩
  simp [canonicalEvenWitnessCandidate, fiberIndex, succPow_pure012_color2, add_assoc]

def trivialBranchPrefixFiberTrackingColor0ArithmeticAt
    (m : Nat) (z : VZ m) : Prop :=
  ∀ t : Nat,
    t < (fiberIndex z).val →
    fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val = t

def trivialBranchPrefixFiberTrackingColor1ArithmeticAt
    (m : Nat) (z : VZ m) : Prop :=
  ∀ t : Nat,
    t < (fiberIndex z).val →
    fiberSum m z.1.val (z.2.1 - fiberIndex z + t).val z.2.2.val = t

def trivialBranchPrefixFiberTrackingColor2ArithmeticAt
    (m : Nat) (z : VZ m) : Prop :=
  ∀ t : Nat,
    t < (fiberIndex z).val →
    fiberSum m z.1.val z.2.1.val (z.2.2 - fiberIndex z + t).val = t

theorem trivialBranchPrefixFiberTrackingColor0At_of_arithmetic
    (m : Nat) (z : VZ m)
    (h : trivialBranchPrefixFiberTrackingColor0ArithmeticAt m z) :
    trivialBranchPrefixFiberTrackingColor0At m z := by
  intro t ht
  rw [pure012_candidate_orbit_color0]
  simpa [trivialBranchPrefixFiberTrackingColor0ArithmeticAt] using h t ht

theorem trivialBranchPrefixFiberTrackingColor1At_of_arithmetic
    (m : Nat) (z : VZ m)
    (h : trivialBranchPrefixFiberTrackingColor1ArithmeticAt m z) :
    trivialBranchPrefixFiberTrackingColor1At m z := by
  intro t ht
  rw [pure012_candidate_orbit_color1]
  simpa [trivialBranchPrefixFiberTrackingColor1ArithmeticAt] using h t ht

theorem trivialBranchPrefixFiberTrackingColor2At_of_arithmetic
    (m : Nat) (z : VZ m)
    (h : trivialBranchPrefixFiberTrackingColor2ArithmeticAt m z) :
    trivialBranchPrefixFiberTrackingColor2At m z := by
  intro t ht
  rw [pure012_candidate_orbit_color2]
  simpa [trivialBranchPrefixFiberTrackingColor2ArithmeticAt] using h t ht

def CanonicalEvenTrivialBranchTrackingArithmeticColorCases (m : Nat) : Prop :=
  ∀ z : VZ m,
    vertexFiberSum m z ≤ m - 3 →
    trivialBranchPrefixFiberTrackingColor0ArithmeticAt m z ∧
    trivialBranchPrefixFiberTrackingColor1ArithmeticAt m z ∧
    trivialBranchPrefixFiberTrackingColor2ArithmeticAt m z

theorem canonicalEvenTrivialBranchTrackingColorCases_of_arithmetic
    (m : Nat)
    (h : CanonicalEvenTrivialBranchTrackingArithmeticColorCases m) :
    CanonicalEvenTrivialBranchTrackingColorCases m := by
  intro z hz
  rcases h z hz with ⟨h0, h1, h2⟩
  constructor
  · exact trivialBranchPrefixFiberTrackingColor0At_of_arithmetic m z h0
  · constructor
    · exact trivialBranchPrefixFiberTrackingColor1At_of_arithmetic m z h1
    · exact trivialBranchPrefixFiberTrackingColor2At_of_arithmetic m z h2

end ClaudeCyclesARZN
