import ClaudeCyclesARZN.EvenRuleWitnessByCases

namespace ClaudeCyclesARZN

/--
Packaged witness obligations for the canonical even rule, color by color.

This is the exact remaining proof target after the branch reduction:
- trivial fibers `s ≤ m-3`,
- exceptional fiber `s = m-2`,
- exceptional fiber `s = m-1`.
-/
def CanonicalEvenWitnessObligations (m : Nat) (c : Color) : Prop :=
  (∀ z : VZ m, vertexFiberSum m z ≤ m - 3 → CanonicalEvenWitnessAt m c z) ∧
  (∀ z : VZ m, vertexFiberSum m z = m - 2 → CanonicalEvenWitnessAt m c z) ∧
  (∀ z : VZ m, vertexFiberSum m z = m - 1 → CanonicalEvenWitnessAt m c z)

/--
All-colors packaged version of the same target.
-/
def CanonicalEvenWitnessObligationsAllColors (m : Nat) : Prop :=
  ∀ c : Color, CanonicalEvenWitnessObligations m c

theorem canonicalEvenWitnessObligations_trivial
    (m : Nat) (c : Color)
    (h : CanonicalEvenWitnessObligations m c) :
    ∀ z : VZ m, vertexFiberSum m z ≤ m - 3 → CanonicalEvenWitnessAt m c z :=
  h.1

theorem canonicalEvenWitnessObligations_msub2
    (m : Nat) (c : Color)
    (h : CanonicalEvenWitnessObligations m c) :
    ∀ z : VZ m, vertexFiberSum m z = m - 2 → CanonicalEvenWitnessAt m c z :=
  h.2.1

theorem canonicalEvenWitnessObligations_msub1
    (m : Nat) (c : Color)
    (h : CanonicalEvenWitnessObligations m c) :
    ∀ z : VZ m, vertexFiberSum m z = m - 1 → CanonicalEvenWitnessAt m c z :=
  h.2.2

theorem canonicalEvenHasIndexedResidualWitnesses_of_obligations
    (m : Nat) (c : Color)
    (hm : admissibleEvenM m)
    (h : CanonicalEvenWitnessObligations m c) :
    CanonicalEvenHasIndexedResidualWitnesses m c := by
  rcases h with ⟨htrivial, hsub2, hsub1⟩
  exact canonicalEvenHasIndexedResidualWitnesses_of_fiberCases
    m c hm htrivial hsub2 hsub1

theorem canonicalEvenHasResidualNormalForm_of_obligations
    (m : Nat) (c : Color)
    (hm : admissibleEvenM m)
    (h : CanonicalEvenWitnessObligations m c) :
    CanonicalEvenHasResidualNormalForm m c := by
  exact canonicalEven_hasResidualNormalForm_of_indexedResidualWitnesses
    m c
    (canonicalEvenHasIndexedResidualWitnesses_of_obligations m c hm h)

theorem canonicalEven_globalReachability_of_obligations
    (m : Nat) (c : Color) (x : FiberZero m)
    (hm : admissibleEvenM m)
    (hret : ReturnOrbitCoversFiberZero (evenRuleLocalRule m) c x)
    (h : CanonicalEvenWitnessObligations m c) :
    GlobalOrbitCoversAllVertices (evenRuleLocalRule m) c x := by
  exact canonicalEven_globalReachability_of_fiberCases
    m c x hm hret
    (canonicalEvenWitnessObligations_trivial m c h)
    (canonicalEvenWitnessObligations_msub2 m c h)
    (canonicalEvenWitnessObligations_msub1 m c h)

theorem canonicalEvenHasResidualNormalForm_allColors_of_obligations
    (m : Nat)
    (hm : admissibleEvenM m)
    (h : CanonicalEvenWitnessObligationsAllColors m) :
    ∀ c : Color, CanonicalEvenHasResidualNormalForm m c := by
  intro c
  exact canonicalEvenHasResidualNormalForm_of_obligations m c hm (h c)

end ClaudeCyclesARZN
