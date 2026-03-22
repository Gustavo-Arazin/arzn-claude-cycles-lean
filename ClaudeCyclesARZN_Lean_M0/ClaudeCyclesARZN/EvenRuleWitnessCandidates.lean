import ClaudeCyclesARZN.EvenRuleWitnessObligations

namespace ClaudeCyclesARZN

/--
Explicit canonical candidate on `F₀` for the indexed residual witness of a target vertex `z`.

For color 0, subtract the fiber index from the first coordinate.
For color 1, subtract it from the second coordinate.
For color 2, subtract it from the third coordinate.

In all cases, the resulting point lies on the reference fiber `F₀`.
-/
def canonicalEvenWitnessCandidate (m : Nat) (c : Color) : VZ m → FiberZero m
  | (i, j, k) =>
      match c.val with
      | 0 =>
          ⟨(i - (i + j + k), j, k), by
            dsimp [Fiber, fiberIndex]
            ring⟩
      | 1 =>
          ⟨(i, j - (i + j + k), k), by
            dsimp [Fiber, fiberIndex]
            ring⟩
      | _ =>
          ⟨(i, j, k - (i + j + k)), by
            dsimp [Fiber, fiberIndex]
            ring⟩

@[simp] theorem canonicalEvenWitnessCandidate_mem
    (m : Nat) (c : Color) (z : VZ m) :
    (canonicalEvenWitnessCandidate m c z).1 ∈ Fiber m 0 :=
  (canonicalEvenWitnessCandidate m c z).2

/--
Pointwise success statement for the explicit candidate.
This is the exact equality that remains to be proved branch by branch.
-/
def canonicalEvenCandidateHits (m : Nat) (c : Color) (z : VZ m) : Prop :=
  (residualMapFromFiberZero
      (evenRuleLocalRule m) c (fiberIndex z).val
      (canonicalEvenWitnessCandidate m c z)).1 = z

theorem canonicalEvenWitnessAt_of_candidateHits
    (m : Nat) (c : Color) (z : VZ m)
    (h : canonicalEvenCandidateHits m c z) :
    CanonicalEvenWitnessAt m c z := by
  exact ⟨canonicalEvenWitnessCandidate m c z, h⟩

/--
If the explicit candidate is shown to hit every target in the three fiber branches,
then all witness obligations are discharged.
-/
theorem canonicalEvenWitnessObligations_of_candidateHits
    (m : Nat) (c : Color)
    (htrivial :
      ∀ z : VZ m, vertexFiberSum m z ≤ m - 3 → canonicalEvenCandidateHits m c z)
    (hsub2 :
      ∀ z : VZ m, vertexFiberSum m z = m - 2 → canonicalEvenCandidateHits m c z)
    (hsub1 :
      ∀ z : VZ m, vertexFiberSum m z = m - 1 → canonicalEvenCandidateHits m c z) :
    CanonicalEvenWitnessObligations m c := by
  constructor
  · intro z hz
    exact canonicalEvenWitnessAt_of_candidateHits m c z (htrivial z hz)
  · constructor
    · intro z hz
      exact canonicalEvenWitnessAt_of_candidateHits m c z (hsub2 z hz)
    · intro z hz
      exact canonicalEvenWitnessAt_of_candidateHits m c z (hsub1 z hz)

theorem canonicalEvenWitnessObligationsAllColors_of_candidateHits
    (m : Nat)
    (h :
      ∀ c : Color,
        (∀ z : VZ m, vertexFiberSum m z ≤ m - 3 → canonicalEvenCandidateHits m c z) ∧
        (∀ z : VZ m, vertexFiberSum m z = m - 2 → canonicalEvenCandidateHits m c z) ∧
        (∀ z : VZ m, vertexFiberSum m z = m - 1 → canonicalEvenCandidateHits m c z)) :
    CanonicalEvenWitnessObligationsAllColors m := by
  intro c
  rcases h c with ⟨htrivial, hsub2, hsub1⟩
  exact canonicalEvenWitnessObligations_of_candidateHits m c htrivial hsub2 hsub1

end ClaudeCyclesARZN
