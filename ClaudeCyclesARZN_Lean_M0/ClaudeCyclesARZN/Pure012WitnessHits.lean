import ClaudeCyclesARZN.Pure012WitnessDynamics

namespace ClaudeCyclesARZN

theorem neZero_of_admissibleEvenM
    (m : Nat) (hm : admissibleEvenM m) : NeZero m := by
  rcases hm with ⟨hm8, _⟩
  exact ⟨by omega⟩

/--
Under the pure `012` dynamics, the explicit candidate on `F₀`
lands exactly on the target vertex.
-/
def pure012CandidateHits (m : Nat) (c : Color) (z : VZ m) : Prop :=
  (residualMapFromFiberZero
      (pure012LocalRule m) c (fiberIndex z).val
      (canonicalEvenWitnessCandidate m c z)).1 = z

theorem pure012CandidateHits_color0
    (m : Nat) (hm : admissibleEvenM m) (z : VZ m) :
    pure012CandidateHits m (0 : Color) z := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  rcases z with ⟨i, j, k⟩
  unfold pure012CandidateHits
  rw [residualMapFromFiberZero_val]
  ext <;>
    simp [canonicalEvenWitnessCandidate, fiberIndex, succPow_pure012_color0]

theorem pure012CandidateHits_color1
    (m : Nat) (hm : admissibleEvenM m) (z : VZ m) :
    pure012CandidateHits m (1 : Color) z := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  rcases z with ⟨i, j, k⟩
  unfold pure012CandidateHits
  rw [residualMapFromFiberZero_val]
  ext <;>
    simp [canonicalEvenWitnessCandidate, fiberIndex, succPow_pure012_color1]

theorem pure012CandidateHits_color2
    (m : Nat) (hm : admissibleEvenM m) (z : VZ m) :
    pure012CandidateHits m (2 : Color) z := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  rcases z with ⟨i, j, k⟩
  unfold pure012CandidateHits
  rw [residualMapFromFiberZero_val]
  ext <;>
    simp [canonicalEvenWitnessCandidate, fiberIndex, succPow_pure012_color2]
  ring

theorem pure012CandidateHits_allColors
    (m : Nat) (hm : admissibleEvenM m) (c : Color) (z : VZ m) :
    pure012CandidateHits m c z := by
  fin_cases c
  · simpa using pure012CandidateHits_color0 m hm z
  · simpa using pure012CandidateHits_color1 m hm z
  · simpa using pure012CandidateHits_color2 m hm z

/--
Penultimate-step form of the pure `012` hit on the final exceptional branch `F_{m-1}`.

This is the exact one-step-before-the-end version of `pure012CandidateHits`:
after `m - 2` residual successor steps from the explicit candidate on `F₀`,
one final pure-`012` successor lands on the target vertex.
-/
def pure012ExceptionalPenultimateMSub1AllColors (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m,
    vertexFiberSum m z = m - 1 →
    succ (pure012LocalRule m) c
      ((residualMapFromFiberZero
        (pure012LocalRule m) c (m - 2)
        (canonicalEvenWitnessCandidate m c z)).1) = z

theorem pure012ExceptionalPenultimateMSub1AllColors_all
    (m : Nat) (hm : admissibleEvenM m) :
    pure012ExceptionalPenultimateMSub1AllColors m := by
  intro c z hz
  have hhits : pure012CandidateHits m c z := by
    exact pure012CandidateHits_allColors m hm c z
  have hfib : (fiberIndex z).val = m - 1 := by
    letI : NeZero m := neZero_of_admissibleEvenM m hm
    rcases z with ⟨i, j, k⟩
    change (i + j + k : ZMod m).val = m - 1
    have hmpos : 0 < m := by
      rcases hm with ⟨hm8, _⟩
      omega
    have hcast :
        (((fiberSum m i.val j.val k.val : Nat) : ZMod m)) = i + j + k := by
      unfold fiberSum
      have hmod :
          ((((i.val + j.val + k.val) % m : Nat) : ZMod m))
            =
          (((i.val + j.val + k.val : Nat) : ZMod m)) := by
        simp
      rw [hmod]
      rw [Nat.cast_add, Nat.cast_add]
      rw [ZMod.natCast_zmod_val i,
          ZMod.natCast_zmod_val j,
          ZMod.natCast_zmod_val k]
    have hlt : fiberSum m i.val j.val k.val < m := by
      unfold fiberSum
      exact Nat.mod_lt _ hmpos
    have hvals :
        (((fiberSum m i.val j.val k.val : Nat) : ZMod m)).val = (i + j + k).val := by
      exact congrArg ZMod.val hcast
    have hval : (i + j + k : ZMod m).val = fiberSum m i.val j.val k.val := by
      rw [ZMod.val_natCast_of_lt hlt] at hvals
      exact hvals.symm
    rw [hval]
    simpa [vertexFiberSum] using hz
  have hmsub : m - 1 = (m - 2) + 1 := by
    rcases hm with ⟨hm8, _⟩
    omega
  unfold pure012CandidateHits at hhits
  rw [hfib, hmsub, residualMapFromFiberZero_val, succPow_succ] at hhits
  simpa [residualMapFromFiberZero_val] using hhits

end ClaudeCyclesARZN
