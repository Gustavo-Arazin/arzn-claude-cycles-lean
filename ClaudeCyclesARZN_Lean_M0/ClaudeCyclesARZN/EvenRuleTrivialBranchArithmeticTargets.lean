import ClaudeCyclesARZN.EvenRuleTrivialBranchOutsideResidual

namespace ClaudeCyclesARZN

/--
Arithmetic bound for the trivial branch:
the target nat-level fiber sum is at most `m - 3`.
-/
def trivialBranchTargetBoundAt
    (m : Nat) (z : VZ m) : Prop :=
  vertexFiberSum m z ≤ m - 3

/--
Arithmetic tracking target for the trivial branch:
along the pure `012` prefix issued from the explicit candidate on `F₀`,
the nat-level fiber sum of the visited point is exactly the time parameter `t`.
-/
def trivialBranchPrefixFiberTrackingAt
    (m : Nat) (c : Color) (z : VZ m) : Prop :=
  ∀ t : Nat,
    t < (fiberIndex z).val →
    let v := succPow (pure012LocalRule m) c t (canonicalEvenWitnessCandidate m c z).1
    fiberSum m v.1.val v.2.1.val v.2.2.val = t

/--
If the pure `012` prefix has nat-level fiber sum exactly `t` at time `t`,
and the target lies in the trivial region `≤ m - 3`,
then the whole relevant prefix stays outside the residual support.
-/
theorem trivialBranchPrefixOutsideResidualAt_of_tracking_and_bound
    (m : Nat) (c : Color) (z : VZ m)
    (hm : admissibleEvenM m)
    (hbound : trivialBranchTargetBoundAt m z)
    (htrack : trivialBranchPrefixFiberTrackingAt m c z) :
    trivialBranchPrefixOutsideResidualAt m c z := by
  intro t ht
  let v := succPow (pure012LocalRule m) c t (canonicalEvenWitnessCandidate m c z).1
  have hm8 : 8 ≤ m := hm.1
  have htle : t ≤ m - 3 := by
    exact Nat.le_trans (Nat.le_of_lt ht) hbound
  have hsum : fiberSum m v.1.val v.2.1.val v.2.2.val = t := by
    simpa [v] using htrack t ht
  apply not_residualSupport_of_le_msub3
    (m := m) (i := v.1.val) (j := v.2.1.val) (k := v.2.2.val) hm8
  rw [hsum]
  exact htle

/--
Packaged arithmetic target for the trivial branch:
for every color and every target in the trivial region, it is enough to provide
- the bound `vertexFiberSum m z ≤ m - 3`,
- and the prefix tracking property for `fiberSum`.
-/
def CanonicalEvenTrivialBranchArithmeticTargets (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m,
    vertexFiberSum m z ≤ m - 3 →
    trivialBranchTargetBoundAt m z ∧
    trivialBranchPrefixFiberTrackingAt m c z

theorem canonicalEvenTrivialBranchCoincidenceAllColors_of_arithmeticTargets
    (m : Nat)
    (hm : admissibleEvenM m)
    (h :
      CanonicalEvenTrivialBranchArithmeticTargets m) :
    CanonicalEvenTrivialBranchCoincidenceAllColors m := by
  intro c z hz
  have hbound : trivialBranchTargetBoundAt m z := (h c z hz).1
  have htrack : trivialBranchPrefixFiberTrackingAt m c z := (h c z hz).2
  have hout :
      trivialBranchPrefixOutsideResidualAt m c z := by
    exact trivialBranchPrefixOutsideResidualAt_of_tracking_and_bound
      m c z hm hbound htrack
  have hprefix :
      trivialBranchPrefixAgreementAt m c z := by
    exact trivialBranchPrefixAgreementAt_of_outsideResidual
      m c z hm hout
  exact trivialBranchPure012CoincidesAt_of_prefixAgreement
    m c z hprefix

theorem canonicalEvenCompletionTargets_of_arithmeticTargets
    (m : Nat)
    (hm : admissibleEvenM m)
    (htriv : CanonicalEvenTrivialBranchArithmeticTargets m)
    (hsub2 :
      ∀ c : Color, ∀ z : VZ m,
        vertexFiberSum m z = m - 2 →
        CanonicalEvenWitnessAt m c z)
    (hsub1 :
      ∀ c : Color, ∀ z : VZ m,
        vertexFiberSum m z = m - 1 →
        CanonicalEvenWitnessAt m c z) :
    CanonicalEvenCompletionTargets m := by
  constructor
  · exact canonicalEvenTrivialBranchCoincidenceAllColors_of_arithmeticTargets
      m hm htriv
  · constructor
    · exact hsub2
    · exact hsub1

theorem canonicalEven_globalReachability_of_arithmeticTargets
    (m : Nat) (c : Color) (x : FiberZero m)
    (hm : admissibleEvenM m)
    (hret : ReturnOrbitCoversFiberZero (evenRuleLocalRule m) c x)
    (htriv : CanonicalEvenTrivialBranchArithmeticTargets m)
    (hsub2 :
      ∀ c : Color, ∀ z : VZ m,
        vertexFiberSum m z = m - 2 →
        CanonicalEvenWitnessAt m c z)
    (hsub1 :
      ∀ c : Color, ∀ z : VZ m,
        vertexFiberSum m z = m - 1 →
        CanonicalEvenWitnessAt m c z) :
    GlobalOrbitCoversAllVertices (evenRuleLocalRule m) c x := by
  exact canonicalEven_globalReachability_of_completionTargets
    m c x hm hret
    (canonicalEvenCompletionTargets_of_arithmeticTargets
      m hm htriv hsub2 hsub1)

end ClaudeCyclesARZN
