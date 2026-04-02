import ClaudeCyclesARZN.EvenRuleTrivialWitnessBridge

namespace ClaudeCyclesARZN

/--
All-colors version of the trivial-branch coincidence target.
This is the remaining obligation for fibers with `s ≤ m - 3`.
-/
def CanonicalEvenTrivialBranchCoincidenceAllColors (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m,
    vertexFiberSum m z ≤ m - 3 →
    trivialBranchPure012CoincidesAt m c z

/--
All-colors version of the two exceptional witness targets.
These are the remaining obligations for the exceptional fibers
`F_{m-2}` and `F_{m-1}`.
-/
def CanonicalEvenExceptionalWitnessesAllColors (m : Nat) : Prop :=
  (∀ c : Color, ∀ z : VZ m,
      vertexFiberSum m z = m - 2 →
      CanonicalEvenWitnessAt m c z) ∧
  (∀ c : Color, ∀ z : VZ m,
      vertexFiberSum m z = m - 1 →
      CanonicalEvenWitnessAt m c z)

/--
Final packaged proof target for the canonical even rule.
Once this is discharged, the abstract strong-reduction pipeline closes.
-/
def CanonicalEvenCompletionTargets (m : Nat) : Prop :=
  CanonicalEvenTrivialBranchCoincidenceAllColors m ∧
  CanonicalEvenExceptionalWitnessesAllColors m

theorem canonicalEvenWitnessObligationsAllColors_of_completionTargets
    (m : Nat)
    (hm : admissibleEvenM m)
    (h : CanonicalEvenCompletionTargets m) :
    CanonicalEvenWitnessObligationsAllColors m := by
  intro c
  rcases h with ⟨htriv, hexc⟩
  rcases hexc with ⟨hsub2, hsub1⟩
  exact canonicalEvenWitnessObligations_of_trivialBranchPure012Coincides
    m c hm
    (htriv c)
    (hsub2 c)
    (hsub1 c)

theorem canonicalEvenHasResidualNormalForm_allColors_of_completionTargets
    (m : Nat)
    (hm : admissibleEvenM m)
    (h : CanonicalEvenCompletionTargets m) :
    ∀ c : Color, CanonicalEvenHasResidualNormalForm m c := by
  intro c
  rcases h with ⟨htriv, hexc⟩
  rcases hexc with ⟨hsub2, hsub1⟩
  exact canonicalEvenHasResidualNormalForm_of_trivialBranchPure012Coincides
    m c hm
    (htriv c)
    (hsub2 c)
    (hsub1 c)

theorem canonicalEven_globalReachability_of_completionTargets
    (m : Nat) (c : Color) (x : FiberZero m)
    (hm : admissibleEvenM m)
    (hret : ReturnOrbitCoversFiberZero (evenRuleLocalRule m) c x)
    (h : CanonicalEvenCompletionTargets m) :
    GlobalOrbitCoversAllVertices (evenRuleLocalRule m) c x := by
  rcases h with ⟨htriv, hexc⟩
  rcases hexc with ⟨hsub2, hsub1⟩
  exact canonicalEven_globalReachability_of_trivialBranchPure012Coincides
    m c x hm hret
    (htriv c)
    (hsub2 c)
    (hsub1 c)

theorem canonicalEven_globalReachability_allColors_of_completionTargets
    (m : Nat)
    (hm : admissibleEvenM m)
    (h : CanonicalEvenCompletionTargets m) :
    ∀ c : Color, ∀ x : FiberZero m,
      ReturnOrbitCoversFiberZero (evenRuleLocalRule m) c x →
      GlobalOrbitCoversAllVertices (evenRuleLocalRule m) c x := by
  intro c x hret
  exact canonicalEven_globalReachability_of_completionTargets m c x hm hret h

/--
Named remaining pointwise target for the final exceptional branch `F_{m-1}`.

At this point in M3, once the trivial branch and the `F_{m-2}` exceptional branch
are discharged, the only proof obligation left is to show that the explicit candidate
hits every target vertex on `F_{m-1}`.
-/
def CanonicalEvenExceptionalCandidateHitsMSub1AllColors (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m,
    vertexFiberSum m z = m - 1 →
    canonicalEvenCandidateHits m c z

theorem canonicalEvenExceptionalWitnesses_msub1_allColors_of_candidateHits
    (m : Nat)
    (hsub1 : CanonicalEvenExceptionalCandidateHitsMSub1AllColors m) :
    ∀ c : Color, ∀ z : VZ m,
      vertexFiberSum m z = m - 1 →
      CanonicalEvenWitnessAt m c z := by
  intro c z hz
  exact canonicalEvenWitnessAt_of_candidateHits m c z (hsub1 c z hz)

theorem canonicalEvenCompletionTargets_of_candidateHitsMSub1
    (m : Nat)
    (htriv : CanonicalEvenTrivialBranchCoincidenceAllColors m)
    (hsub2 :
      ∀ c : Color, ∀ z : VZ m,
        vertexFiberSum m z = m - 2 →
        CanonicalEvenWitnessAt m c z)
    (hsub1 : CanonicalEvenExceptionalCandidateHitsMSub1AllColors m) :
    CanonicalEvenCompletionTargets m := by
  refine ⟨htriv, ?_⟩
  exact ⟨hsub2, canonicalEvenExceptionalWitnesses_msub1_allColors_of_candidateHits m hsub1⟩

end ClaudeCyclesARZN
