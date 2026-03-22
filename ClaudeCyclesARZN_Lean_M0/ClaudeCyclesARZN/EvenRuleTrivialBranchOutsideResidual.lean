import ClaudeCyclesARZN.EvenRuleTrivialBranchReduction

namespace ClaudeCyclesARZN

/--
Pointwise outside-residual target for the trivial branch.

Along the pure `012` prefix issued from the explicit witness candidate on `F₀`,
every visited point stays outside the residual support.
-/
def trivialBranchPrefixOutsideResidualAt
    (m : Nat) (c : Color) (z : VZ m) : Prop :=
  ∀ t : Nat,
    t < (fiberIndex z).val →
    let v := succPow (pure012LocalRule m) c t (canonicalEvenWitnessCandidate m c z).1
    residualSupport m v.1.val v.2.1.val v.2.2.val = false

/--
If the pure `012` prefix stays outside the residual support, then the concrete
canonical even rule agrees with the pure `012` rule along that whole prefix.
-/
theorem trivialBranchPrefixAgreementAt_of_outsideResidual
    (m : Nat) (c : Color) (z : VZ m)
    (hm : admissibleEvenM m)
    (hout : trivialBranchPrefixOutsideResidualAt m c z) :
    trivialBranchPrefixAgreementAt m c z := by
  intro t ht
  let v := succPow (pure012LocalRule m) c t (canonicalEvenWitnessCandidate m c z).1
  have hfalse : residualSupport m v.1.val v.2.1.val v.2.2.val = false :=
    hout t ht
  have hconcrete :
      evenRuleLocalRule m v c = axisOfLocalPerm LocalPerm.p012 c := by
    exact evenRuleLocalRule_of_not_residualSupport m v hm c hfalse
  have hpure :
      pure012LocalRule m v c = axisOfLocalPerm LocalPerm.p012 c := by
    simp [pure012LocalRule]
  exact hconcrete.trans hpure.symm

/--
All-colors packaged outside-residual target for the trivial branch.
-/
def CanonicalEvenTrivialBranchPrefixOutsideResidualAllColors (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m, trivialBranchPrefixOutsideResidualAt m c z

theorem canonicalEvenTrivialBranchPrefixAgreementAllColors_of_outsideResidual
    (m : Nat)
    (hm : admissibleEvenM m)
    (h : CanonicalEvenTrivialBranchPrefixOutsideResidualAllColors m) :
    CanonicalEvenTrivialBranchPrefixAgreementAllColors m := by
  intro c z
  exact trivialBranchPrefixAgreementAt_of_outsideResidual m c z hm (h c z)

theorem canonicalEvenTrivialBranchCoincidenceAllColors_of_outsideResidual
    (m : Nat)
    (hm : admissibleEvenM m)
    (h : CanonicalEvenTrivialBranchPrefixOutsideResidualAllColors m) :
    CanonicalEvenTrivialBranchCoincidenceAllColors m := by
  apply canonicalEvenTrivialBranchCoincidenceAllColors_of_prefixAgreement
  exact canonicalEvenTrivialBranchPrefixAgreementAllColors_of_outsideResidual m hm h

end ClaudeCyclesARZN
