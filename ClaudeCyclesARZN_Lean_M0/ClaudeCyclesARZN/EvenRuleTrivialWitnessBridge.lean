import ClaudeCyclesARZN.Pure012WitnessHits

namespace ClaudeCyclesARZN

/--
Pointwise coincidence target for the trivial branch.

At a target vertex `z`, the indexed residual lift for the concrete canonical even rule
is required to agree with the indexed residual lift for the pure `012` rule, when both
start from the same explicit candidate on `F₀`.
-/
def trivialBranchPure012CoincidesAt
    (m : Nat) (c : Color) (z : VZ m) : Prop :=
  (residualMapFromFiberZero
      (evenRuleLocalRule m) c (fiberIndex z).val
      (canonicalEvenWitnessCandidate m c z)).1 =
  (residualMapFromFiberZero
      (pure012LocalRule m) c (fiberIndex z).val
      (canonicalEvenWitnessCandidate m c z)).1

/--
Once the concrete trivial branch agrees with the pure `012` residual lift at `z`,
the explicit candidate is a valid canonical-even witness for `z`.
-/
theorem canonicalEvenWitnessAt_of_trivialBranchPure012Coincides
    (m : Nat) (c : Color) (hm : admissibleEvenM m) (z : VZ m)
    (hcoinc : trivialBranchPure012CoincidesAt m c z) :
    CanonicalEvenWitnessAt m c z := by
  refine ⟨canonicalEvenWitnessCandidate m c z, ?_⟩
  calc
    (residualMapFromFiberZero
        (evenRuleLocalRule m) c (fiberIndex z).val
        (canonicalEvenWitnessCandidate m c z)).1
        =
    (residualMapFromFiberZero
        (pure012LocalRule m) c (fiberIndex z).val
        (canonicalEvenWitnessCandidate m c z)).1 := hcoinc
    _ = z := pure012CandidateHits_allColors m hm c z

/--
Trivial-fiber witness obligation reduced to pointwise coincidence with the pure `012` lift.
-/
theorem canonicalEven_trivialWitnessObligation_of_trivialBranchPure012Coincides
    (m : Nat) (c : Color) (hm : admissibleEvenM m)
    (hcoinc :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchPure012CoincidesAt m c z) :
    ∀ z : VZ m, vertexFiberSum m z ≤ m - 3 → CanonicalEvenWitnessAt m c z := by
  intro z hz
  exact canonicalEvenWitnessAt_of_trivialBranchPure012Coincides
    m c hm z (hcoinc z hz)

/--
Packaged witness obligations: it remains to supply
- coincidence with pure `012` on the trivial branch,
- direct witnesses on the two exceptional branches.
-/
theorem canonicalEvenWitnessObligations_of_trivialBranchPure012Coincides
    (m : Nat) (c : Color) (hm : admissibleEvenM m)
    (hcoinc :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchPure012CoincidesAt m c z)
    (hsub2 :
      ∀ z : VZ m,
        vertexFiberSum m z = m - 2 →
        CanonicalEvenWitnessAt m c z)
    (hsub1 :
      ∀ z : VZ m,
        vertexFiberSum m z = m - 1 →
        CanonicalEvenWitnessAt m c z) :
    CanonicalEvenWitnessObligations m c := by
  constructor
  · exact
      canonicalEven_trivialWitnessObligation_of_trivialBranchPure012Coincides
        m c hm hcoinc
  · constructor
    · exact hsub2
    · exact hsub1

theorem canonicalEvenHasResidualNormalForm_of_trivialBranchPure012Coincides
    (m : Nat) (c : Color) (hm : admissibleEvenM m)
    (hcoinc :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchPure012CoincidesAt m c z)
    (hsub2 :
      ∀ z : VZ m,
        vertexFiberSum m z = m - 2 →
        CanonicalEvenWitnessAt m c z)
    (hsub1 :
      ∀ z : VZ m,
        vertexFiberSum m z = m - 1 →
        CanonicalEvenWitnessAt m c z) :
    CanonicalEvenHasResidualNormalForm m c := by
  exact canonicalEvenHasResidualNormalForm_of_obligations
    m c hm
    (canonicalEvenWitnessObligations_of_trivialBranchPure012Coincides
      m c hm hcoinc hsub2 hsub1)

theorem canonicalEven_globalReachability_of_trivialBranchPure012Coincides
    (m : Nat) (c : Color) (x : FiberZero m)
    (hm : admissibleEvenM m)
    (hret : ReturnOrbitCoversFiberZero (evenRuleLocalRule m) c x)
    (hcoinc :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchPure012CoincidesAt m c z)
    (hsub2 :
      ∀ z : VZ m,
        vertexFiberSum m z = m - 2 →
        CanonicalEvenWitnessAt m c z)
    (hsub1 :
      ∀ z : VZ m,
        vertexFiberSum m z = m - 1 →
        CanonicalEvenWitnessAt m c z) :
    GlobalOrbitCoversAllVertices (evenRuleLocalRule m) c x := by
  exact canonicalEven_globalReachability_of_obligations
    m c x hm hret
    (canonicalEvenWitnessObligations_of_trivialBranchPure012Coincides
      m c hm hcoinc hsub2 hsub1)

end ClaudeCyclesARZN
