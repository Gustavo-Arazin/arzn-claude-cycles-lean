import ClaudeCyclesARZN.EvenRuleLocalResidualNormalForm
import ClaudeCyclesARZN.StrongReduction

namespace ClaudeCyclesARZN

/--
It is enough to build residual witnesses using the target fiber index itself.
-/
def HasIndexedResidualWitnesses {m : Nat} (σ : LocalRule m) (c : Color) : Prop :=
  ∀ z : VZ m, ∃ y : FiberZero m,
    (residualMapFromFiberZero σ c (fiberIndex z).val y).1 = z

theorem hasResidualNormalForm_of_hasIndexedResidualWitnesses
    {m : Nat} {σ : LocalRule m} {c : Color}
    (h : HasIndexedResidualWitnesses σ c) :
    HasResidualNormalForm σ c := by
  intro z
  rcases h z with ⟨y, hy⟩
  exact ⟨(fiberIndex z).val, y, hy⟩

/--
Canonical-even specialization of indexed residual witnesses.
-/
def CanonicalEvenHasIndexedResidualWitnesses (m : Nat) (c : Color) : Prop :=
  HasIndexedResidualWitnesses (evenRuleLocalRule m) c

/--
Canonical-even specialization of residual normal form.
-/
def CanonicalEvenHasResidualNormalForm (m : Nat) (c : Color) : Prop :=
  HasResidualNormalForm (evenRuleLocalRule m) c

theorem canonicalEven_hasResidualNormalForm_of_indexedResidualWitnesses
    (m : Nat) (c : Color)
    (h : CanonicalEvenHasIndexedResidualWitnesses m c) :
    CanonicalEvenHasResidualNormalForm m c := by
  exact hasResidualNormalForm_of_hasIndexedResidualWitnesses h

theorem canonicalEven_strongReduction_globalReachability
    (m : Nat) (c : Color) (x : FiberZero m)
    (hret : ReturnOrbitCoversFiberZero (evenRuleLocalRule m) c x)
    (hnf : CanonicalEvenHasResidualNormalForm m c) :
    GlobalOrbitCoversAllVertices (evenRuleLocalRule m) c x := by
  exact strongReduction_globalReachability
    (σ := evenRuleLocalRule m) (c := c) (x := x) hret hnf

theorem canonicalEven_globalReachability_of_indexedResidualWitnesses
    (m : Nat) (c : Color) (x : FiberZero m)
    (hret : ReturnOrbitCoversFiberZero (evenRuleLocalRule m) c x)
    (hw : CanonicalEvenHasIndexedResidualWitnesses m c) :
    GlobalOrbitCoversAllVertices (evenRuleLocalRule m) c x := by
  apply canonicalEven_strongReduction_globalReachability (m := m) (c := c) (x := x) hret
  exact canonicalEven_hasResidualNormalForm_of_indexedResidualWitnesses m c hw

end ClaudeCyclesARZN
