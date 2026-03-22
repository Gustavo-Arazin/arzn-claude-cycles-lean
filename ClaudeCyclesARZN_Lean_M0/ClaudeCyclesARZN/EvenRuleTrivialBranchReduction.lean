import ClaudeCyclesARZN.EvenRuleTrivialWitnessBridge

namespace ClaudeCyclesARZN

theorem succ_eq_of_rule_eq
    {m : Nat} (σ τ : LocalRule m) (c : Color) (v : VZ m)
    (h : σ v c = τ v c) :
    succ σ c v = succ τ c v := by
  simp [succ, h]

/--
If two local rules agree on every point of the reference orbit prefix of length `n`,
then their `succPow` iterates agree at time `n`.
-/
theorem succPow_eq_of_prefixAgreement
    {m : Nat} (σ τ : LocalRule m) (c : Color) (x : VZ m) :
    ∀ n : Nat,
      (∀ t : Nat, t < n → σ (succPow τ c t x) c = τ (succPow τ c t x) c) →
      succPow σ c n x = succPow τ c n x
  | 0, _ => by
      simp [succPow]
  | n + 1, h => by
      have hprefix :
          ∀ t : Nat, t < n → σ (succPow τ c t x) c = τ (succPow τ c t x) c := by
        intro t ht
        exact h t (Nat.lt_trans ht (Nat.lt_succ_self n))
      have ih :
          succPow σ c n x = succPow τ c n x :=
        succPow_eq_of_prefixAgreement σ τ c x n hprefix
      have hstep :
          σ (succPow τ c n x) c = τ (succPow τ c n x) c :=
        h n (Nat.lt_succ_self n)
      rw [succPow_succ, succPow_succ, ih]
      exact succ_eq_of_rule_eq σ τ c (succPow τ c n x) hstep

/--
Prefix agreement target for the trivial branch:
along the pure `012` orbit segment from the explicit candidate on `F₀`,
the concrete canonical even rule chooses the same axis as the pure `012` rule.
-/
def trivialBranchPrefixAgreementAt
    (m : Nat) (c : Color) (z : VZ m) : Prop :=
  ∀ t : Nat,
    t < (fiberIndex z).val →
    evenRuleLocalRule m
      (succPow (pure012LocalRule m) c t (canonicalEvenWitnessCandidate m c z).1) c
      =
    pure012LocalRule m
      (succPow (pure012LocalRule m) c t (canonicalEvenWitnessCandidate m c z).1) c

/--
Once the concrete rule agrees with the pure `012` rule along the whole relevant prefix,
the indexed residual lifts coincide at the target.
-/
theorem trivialBranchPure012CoincidesAt_of_prefixAgreement
    (m : Nat) (c : Color) (z : VZ m)
    (hprefix : trivialBranchPrefixAgreementAt m c z) :
    trivialBranchPure012CoincidesAt m c z := by
  unfold trivialBranchPure012CoincidesAt
  rw [residualMapFromFiberZero_val, residualMapFromFiberZero_val]
  exact succPow_eq_of_prefixAgreement
    (evenRuleLocalRule m)
    (pure012LocalRule m)
    c
    (canonicalEvenWitnessCandidate m c z).1
    (fiberIndex z).val
    hprefix

/--
All-colors packaged version of the same reduction.
-/
def CanonicalEvenTrivialBranchPrefixAgreementAllColors (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m, trivialBranchPrefixAgreementAt m c z

theorem canonicalEvenTrivialBranchCoincidenceAllColors_of_prefixAgreement
    (m : Nat)
    (h : CanonicalEvenTrivialBranchPrefixAgreementAllColors m) :
    CanonicalEvenTrivialBranchCoincidenceAllColors m := by
  intro c z hz
  exact trivialBranchPure012CoincidesAt_of_prefixAgreement m c z (h c z)

end ClaudeCyclesARZN
