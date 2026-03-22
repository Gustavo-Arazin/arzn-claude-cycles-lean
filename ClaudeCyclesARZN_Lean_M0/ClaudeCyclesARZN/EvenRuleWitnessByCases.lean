import ClaudeCyclesARZN.EvenRuleWitnessTargets

namespace ClaudeCyclesARZN

/--
Raw nat-level fiber sum of a `VZ m` vertex, read through canonical representatives.
This is the same coordinate summary already used by the M3 even-rule artifacts.
-/
def vertexFiberSum (m : Nat) (z : VZ m) : Nat :=
  fiberSum m z.1.val z.2.1.val z.2.2.val

theorem vertexFiberSum_lt
    (m : Nat) (z : VZ m)
    (hm : admissibleEvenM m) :
    vertexFiberSum m z < m := by
  rcases hm with ⟨hm8, _⟩
  have hmpos : 0 < m := by
    omega
  unfold vertexFiberSum fiberSum
  exact Nat.mod_lt _ hmpos

/--
To build canonical-even witness targets for all vertices, it is enough to handle
the three fiber cases singled out by the M3 normal form:
- trivial fibers `s ≤ m-3`,
- the exceptional fiber `s = m-2`,
- the exceptional fiber `s = m-1`.
-/
theorem canonicalEvenWitnessAt_of_fiberCases
    (m : Nat) (c : Color)
    (hm : admissibleEvenM m)
    (htrivial :
      ∀ z : VZ m, vertexFiberSum m z ≤ m - 3 → CanonicalEvenWitnessAt m c z)
    (hsub2 :
      ∀ z : VZ m, vertexFiberSum m z = m - 2 → CanonicalEvenWitnessAt m c z)
    (hsub1 :
      ∀ z : VZ m, vertexFiberSum m z = m - 1 → CanonicalEvenWitnessAt m c z) :
    ∀ z : VZ m, CanonicalEvenWitnessAt m c z := by
  intro z
  have hlt : vertexFiberSum m z < m :=
    vertexFiberSum_lt m z hm
  by_cases hs2 : vertexFiberSum m z = m - 2
  · exact hsub2 z hs2
  · by_cases hs1 : vertexFiberSum m z = m - 1
    · exact hsub1 z hs1
    · exact htrivial z (by omega)

/--
Packaged indexed-witness version of the same reduction.
-/
theorem canonicalEvenHasIndexedResidualWitnesses_of_fiberCases
    (m : Nat) (c : Color)
    (hm : admissibleEvenM m)
    (htrivial :
      ∀ z : VZ m, vertexFiberSum m z ≤ m - 3 → CanonicalEvenWitnessAt m c z)
    (hsub2 :
      ∀ z : VZ m, vertexFiberSum m z = m - 2 → CanonicalEvenWitnessAt m c z)
    (hsub1 :
      ∀ z : VZ m, vertexFiberSum m z = m - 1 → CanonicalEvenWitnessAt m c z) :
    CanonicalEvenHasIndexedResidualWitnesses m c := by
  intro z
  exact canonicalEvenWitnessAt_of_fiberCases m c hm htrivial hsub2 hsub1 z

/--
Consequently, the same three branch obligations are enough to establish the
abstract residual-normal-form hypothesis for the canonical even rule.
-/
theorem canonicalEvenHasResidualNormalForm_of_fiberCases
    (m : Nat) (c : Color)
    (hm : admissibleEvenM m)
    (htrivial :
      ∀ z : VZ m, vertexFiberSum m z ≤ m - 3 → CanonicalEvenWitnessAt m c z)
    (hsub2 :
      ∀ z : VZ m, vertexFiberSum m z = m - 2 → CanonicalEvenWitnessAt m c z)
    (hsub1 :
      ∀ z : VZ m, vertexFiberSum m z = m - 1 → CanonicalEvenWitnessAt m c z) :
    CanonicalEvenHasResidualNormalForm m c := by
  apply canonicalEven_hasResidualNormalForm_of_indexedResidualWitnesses
  exact canonicalEvenHasIndexedResidualWitnesses_of_fiberCases
    m c hm htrivial hsub2 hsub1

/--
Strong-reduction corollary in branch-reduced form.
Once the three witness obligations are discharged, global reachability follows
from return-orbit coverage on `F₀`.
-/
theorem canonicalEven_globalReachability_of_fiberCases
    (m : Nat) (c : Color) (x : FiberZero m)
    (hm : admissibleEvenM m)
    (hret : ReturnOrbitCoversFiberZero (evenRuleLocalRule m) c x)
    (htrivial :
      ∀ z : VZ m, vertexFiberSum m z ≤ m - 3 → CanonicalEvenWitnessAt m c z)
    (hsub2 :
      ∀ z : VZ m, vertexFiberSum m z = m - 2 → CanonicalEvenWitnessAt m c z)
    (hsub1 :
      ∀ z : VZ m, vertexFiberSum m z = m - 1 → CanonicalEvenWitnessAt m c z) :
    GlobalOrbitCoversAllVertices (evenRuleLocalRule m) c x := by
  apply canonicalEven_globalReachability_of_pointwiseWitnesses
    (m := m) (c := c) (x := x) hret
  exact canonicalEvenWitnessAt_of_fiberCases m c hm htrivial hsub2 hsub1

end ClaudeCyclesARZN
