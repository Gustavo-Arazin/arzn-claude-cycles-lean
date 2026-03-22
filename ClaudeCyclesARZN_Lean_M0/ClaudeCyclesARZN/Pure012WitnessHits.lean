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

end ClaudeCyclesARZN
