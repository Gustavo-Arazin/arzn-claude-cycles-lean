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

end ClaudeCyclesARZN
