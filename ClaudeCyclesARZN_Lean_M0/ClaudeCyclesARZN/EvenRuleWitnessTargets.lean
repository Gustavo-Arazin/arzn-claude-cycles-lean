import ClaudeCyclesARZN.EvenRuleStrongReduction

namespace ClaudeCyclesARZN

/--
Pointwise witness target for the canonical even rule.

For a target vertex `z`, it is enough to find a point `y` on the reference fiber `F₀`
whose indexed residual lift lands exactly at `z`.
-/
def CanonicalEvenWitnessAt (m : Nat) (c : Color) (z : VZ m) : Prop :=
  ∃ y : FiberZero m,
    (residualMapFromFiberZero (evenRuleLocalRule m) c (fiberIndex z).val y).1 = z

theorem canonicalEvenHasIndexedResidualWitnesses_iff
    (m : Nat) (c : Color) :
    CanonicalEvenHasIndexedResidualWitnesses m c ↔
      ∀ z : VZ m, CanonicalEvenWitnessAt m c z := by
  rfl

theorem canonicalEven_hasResidualNormalForm_of_pointwiseWitnesses
    (m : Nat) (c : Color)
    (h : ∀ z : VZ m, CanonicalEvenWitnessAt m c z) :
    CanonicalEvenHasResidualNormalForm m c := by
  exact canonicalEven_hasResidualNormalForm_of_indexedResidualWitnesses m c h

theorem canonicalEven_pointwiseReachability_of_witness
    (m : Nat) (c : Color) (x : FiberZero m)
    (hret : ReturnOrbitCoversFiberZero (evenRuleLocalRule m) c x)
    {z : VZ m}
    (hz : CanonicalEvenWitnessAt m c z) :
    ReachesBySucc (evenRuleLocalRule m) c x.1 z := by
  rcases hz with ⟨y, hy⟩
  exact strongReduction_pointwise
    (σ := evenRuleLocalRule m) (c := c) (x := x) hret
    ⟨(fiberIndex z).val, y, hy⟩

theorem canonicalEven_globalReachability_of_pointwiseWitnesses
    (m : Nat) (c : Color) (x : FiberZero m)
    (hret : ReturnOrbitCoversFiberZero (evenRuleLocalRule m) c x)
    (h : ∀ z : VZ m, CanonicalEvenWitnessAt m c z) :
    GlobalOrbitCoversAllVertices (evenRuleLocalRule m) c x := by
  exact canonicalEven_globalReachability_of_indexedResidualWitnesses m c x hret h

end ClaudeCyclesARZN
