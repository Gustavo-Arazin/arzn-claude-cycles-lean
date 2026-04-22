import ClaudeCyclesARZN.EvenRuleTrivialBranchTrackingColor0

namespace ClaudeCyclesARZN

/--
Exact modular core still needed to prove the color-0 tracking target.

This isolates the remaining difficulty in its cleanest form:
the nat-level tracking statement will follow once this equality in `ZMod m`
is available pointwise.
-/
def CanonicalEvenTrivialBranchTrackingColor0ModCore (m : Nat) : Prop :=
  ∀ z : VZ m, ∀ t : Nat,
    t < (fiberIndex z).val →
    ((fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val : Nat) : ZMod m)
      = (t : ZMod m)

theorem canonicalEvenTrivialBranchTrackingColor0Target_of_modCore
    (m : Nat) (hm : admissibleEvenM m)
    (hcore : CanonicalEvenTrivialBranchTrackingColor0ModCore m) :
    CanonicalEvenTrivialBranchTrackingColor0Target m := by
  intro z hz t ht
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  have hmpos : 0 < m := by
    rcases hm with ⟨hm8, _⟩
    omega
  have hmod :
      ((fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val : Nat) : ZMod m)
        = (t : ZMod m) := by
    exact hcore z t ht
  have hleftlt :
      fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val < m := by
    unfold fiberSum
    exact Nat.mod_lt _ hmpos
  have hfiblt : (fiberIndex z).val < m := by
    simpa using (ZMod.val_lt (fiberIndex z))
  have htm : t < m := Nat.lt_trans ht hfiblt
  have hvals :
      (((fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val : Nat) : ZMod m)).val
        = ((t : ZMod m)).val := by
    exact congrArg ZMod.val hmod
  have hleftval :
      (((fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val : Nat) : ZMod m)).val
        =
      fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val := by
    exact ZMod.val_natCast_of_lt hleftlt
  have htval : ((t : ZMod m)).val = t := by
    exact ZMod.val_natCast_of_lt htm
  rw [hleftval, htval] at hvals
  exact hvals

theorem canonicalEvenTrivialBranchTrackingColor0ModCore_all
    (m : Nat) (hm : admissibleEvenM m) :
    CanonicalEvenTrivialBranchTrackingColor0ModCore m := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  intro z t ht
  rcases z with ⟨i, j, k⟩
  change ((fiberSum m (i - (i + j + k) + (t : ZMod m)).val j.val k.val : Nat) : ZMod m) = (t : ZMod m)
  unfold fiberSum
  have hcastmod :
      ((((i - (i + j + k) + (t : ZMod m)).val + j.val + k.val) % m : Nat) : ZMod m)
        =
      ((((i - (i + j + k) + (t : ZMod m)).val + j.val + k.val : Nat)) : ZMod m) := by
    simp
  rw [hcastmod]
  rw [Nat.cast_add, Nat.cast_add]
  rw [ZMod.natCast_zmod_val (i - (i + j + k) + (t : ZMod m)),
      ZMod.natCast_zmod_val j,
      ZMod.natCast_zmod_val k]
  ring_nf

theorem canonicalEvenTrivialBranchTrackingColor0Target_all
    (m : Nat) (hm : admissibleEvenM m) :
    CanonicalEvenTrivialBranchTrackingColor0Target m := by
  exact canonicalEvenTrivialBranchTrackingColor0Target_of_modCore
    m hm
    (canonicalEvenTrivialBranchTrackingColor0ModCore_all m hm)

/--
Exact modular core still needed to prove the color-1 tracking target.

This is the color-1 analogue of the color-0 modular reduction:
the nat-level tracking statement follows once the corresponding equality
in `ZMod m` is available pointwise.
-/
def CanonicalEvenTrivialBranchTrackingColor1ModCore (m : Nat) : Prop :=
  ∀ z : VZ m, ∀ t : Nat,
    t < (fiberIndex z).val →
    ((fiberSum m z.1.val (z.2.1 - fiberIndex z + t).val z.2.2.val : Nat) : ZMod m)
      = (t : ZMod m)

theorem canonicalEvenTrivialBranchTrackingColor1Target_of_modCore
    (m : Nat) (hm : admissibleEvenM m)
    (hcore : CanonicalEvenTrivialBranchTrackingColor1ModCore m) :
    ∀ z : VZ m,
      vertexFiberSum m z ≤ m - 3 →
      trivialBranchPrefixFiberTrackingColor1ArithmeticAt m z := by
  intro z hz t ht
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  have hmpos : 0 < m := by
    rcases hm with ⟨hm8, _⟩
    omega
  have hmod :
      ((fiberSum m z.1.val (z.2.1 - fiberIndex z + t).val z.2.2.val : Nat) : ZMod m)
        = (t : ZMod m) := by
    exact hcore z t ht
  have hleftlt :
      fiberSum m z.1.val (z.2.1 - fiberIndex z + t).val z.2.2.val < m := by
    unfold fiberSum
    exact Nat.mod_lt _ hmpos
  have hfiblt : (fiberIndex z).val < m := by
    simpa using (ZMod.val_lt (fiberIndex z))
  have htm : t < m := Nat.lt_trans ht hfiblt
  have hvals :
      (((fiberSum m z.1.val (z.2.1 - fiberIndex z + t).val z.2.2.val : Nat) : ZMod m)).val
        = ((t : ZMod m)).val := by
    exact congrArg ZMod.val hmod
  have hleftval :
      (((fiberSum m z.1.val (z.2.1 - fiberIndex z + t).val z.2.2.val : Nat) : ZMod m)).val
        =
      fiberSum m z.1.val (z.2.1 - fiberIndex z + t).val z.2.2.val := by
    exact ZMod.val_natCast_of_lt hleftlt
  have htval : ((t : ZMod m)).val = t := by
    exact ZMod.val_natCast_of_lt htm
  rw [hleftval, htval] at hvals
  exact hvals

theorem canonicalEvenTrivialBranchTrackingColor1ModCore_all
    (m : Nat) (hm : admissibleEvenM m) :
    CanonicalEvenTrivialBranchTrackingColor1ModCore m := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  intro z t ht
  rcases z with ⟨i, j, k⟩
  change
    ((fiberSum m i.val (j - (i + j + k) + (t : ZMod m)).val k.val : Nat) : ZMod m)
      = (t : ZMod m)
  unfold fiberSum
  have hcastmod :
      (((i.val + (j - (i + j + k) + (t : ZMod m)).val + k.val) % m : Nat) : ZMod m)
        =
      (((i.val + (j - (i + j + k) + (t : ZMod m)).val + k.val : Nat)) : ZMod m) := by
    simp
  rw [hcastmod]
  rw [Nat.cast_add, Nat.cast_add]
  rw [ZMod.natCast_zmod_val i,
      ZMod.natCast_zmod_val (j - (i + j + k) + (t : ZMod m)),
      ZMod.natCast_zmod_val k]
  ring_nf

theorem canonicalEvenTrivialBranchTrackingColor1Target_all
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ z : VZ m,
      vertexFiberSum m z ≤ m - 3 →
      trivialBranchPrefixFiberTrackingColor1ArithmeticAt m z := by
  exact canonicalEvenTrivialBranchTrackingColor1Target_of_modCore
    m hm
    (canonicalEvenTrivialBranchTrackingColor1ModCore_all m hm)

/--
Exact modular core still needed to prove the color-2 tracking target.

This is the color-2 analogue of the previous modular reductions:
the nat-level tracking statement follows once the corresponding equality
in `ZMod m` is available pointwise.
-/
def CanonicalEvenTrivialBranchTrackingColor2ModCore (m : Nat) : Prop :=
  ∀ z : VZ m, ∀ t : Nat,
    t < (fiberIndex z).val →
    ((fiberSum m z.1.val z.2.1.val (z.2.2 - fiberIndex z + t).val : Nat) : ZMod m)
      = (t : ZMod m)

theorem canonicalEvenTrivialBranchTrackingColor2Target_of_modCore
    (m : Nat) (hm : admissibleEvenM m)
    (hcore : CanonicalEvenTrivialBranchTrackingColor2ModCore m) :
    ∀ z : VZ m,
      vertexFiberSum m z ≤ m - 3 →
      trivialBranchPrefixFiberTrackingColor2ArithmeticAt m z := by
  intro z hz t ht
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  have hmpos : 0 < m := by
    rcases hm with ⟨hm8, _⟩
    omega
  have hmod :
      ((fiberSum m z.1.val z.2.1.val (z.2.2 - fiberIndex z + t).val : Nat) : ZMod m)
        = (t : ZMod m) := by
    exact hcore z t ht
  have hleftlt :
      fiberSum m z.1.val z.2.1.val (z.2.2 - fiberIndex z + t).val < m := by
    unfold fiberSum
    exact Nat.mod_lt _ hmpos
  have hfiblt : (fiberIndex z).val < m := by
    simpa using (ZMod.val_lt (fiberIndex z))
  have htm : t < m := Nat.lt_trans ht hfiblt
  have hvals :
      (((fiberSum m z.1.val z.2.1.val (z.2.2 - fiberIndex z + t).val : Nat) : ZMod m)).val
        = ((t : ZMod m)).val := by
    exact congrArg ZMod.val hmod
  have hleftval :
      (((fiberSum m z.1.val z.2.1.val (z.2.2 - fiberIndex z + t).val : Nat) : ZMod m)).val
        =
      fiberSum m z.1.val z.2.1.val (z.2.2 - fiberIndex z + t).val := by
    exact ZMod.val_natCast_of_lt hleftlt
  have htval : ((t : ZMod m)).val = t := by
    exact ZMod.val_natCast_of_lt htm
  rw [hleftval, htval] at hvals
  exact hvals

theorem canonicalEvenTrivialBranchTrackingColor2ModCore_all
    (m : Nat) (hm : admissibleEvenM m) :
    CanonicalEvenTrivialBranchTrackingColor2ModCore m := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  intro z t ht
  rcases z with ⟨i, j, k⟩
  change
    ((fiberSum m i.val j.val (k - (i + j + k) + (t : ZMod m)).val : Nat) : ZMod m)
      = (t : ZMod m)
  unfold fiberSum
  have hcastmod :
      (((i.val + j.val + (k - (i + j + k) + (t : ZMod m)).val) % m : Nat) : ZMod m)
        =
      (((i.val + j.val + (k - (i + j + k) + (t : ZMod m)).val : Nat)) : ZMod m) := by
    simp
  rw [hcastmod]
  rw [Nat.cast_add, Nat.cast_add]
  rw [ZMod.natCast_zmod_val i,
      ZMod.natCast_zmod_val j,
      ZMod.natCast_zmod_val (k - (i + j + k) + (t : ZMod m))]
  ring_nf

theorem canonicalEvenTrivialBranchTrackingColor2Target_all
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ z : VZ m,
      vertexFiberSum m z ≤ m - 3 →
      trivialBranchPrefixFiberTrackingColor2ArithmeticAt m z := by
  exact canonicalEvenTrivialBranchTrackingColor2Target_of_modCore
    m hm
    (canonicalEvenTrivialBranchTrackingColor2ModCore_all m hm)

theorem canonicalEvenTrivialBranchTrackingColor0Arithmetic_all
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ z : VZ m, trivialBranchPrefixFiberTrackingColor0ArithmeticAt m z := by
  intro z t ht
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  have hmpos : 0 < m := by
    rcases hm with ⟨hm8, _⟩
    omega
  have hmod :
      ((fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val : Nat) : ZMod m)
        = (t : ZMod m) := by
    exact canonicalEvenTrivialBranchTrackingColor0ModCore_all m hm z t ht
  have hleftlt :
      fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val < m := by
    unfold fiberSum
    exact Nat.mod_lt _ hmpos
  have hfiblt : (fiberIndex z).val < m := by
    simpa using (ZMod.val_lt (fiberIndex z))
  have htm : t < m := Nat.lt_trans ht hfiblt
  have hvals :
      (((fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val : Nat) : ZMod m)).val
        = ((t : ZMod m)).val := by
    exact congrArg ZMod.val hmod
  have hleftval :
      (((fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val : Nat) : ZMod m)).val
        =
      fiberSum m (z.1 - fiberIndex z + t).val z.2.1.val z.2.2.val := by
    exact ZMod.val_natCast_of_lt hleftlt
  have htval : ((t : ZMod m)).val = t := by
    exact ZMod.val_natCast_of_lt htm
  rw [hleftval, htval] at hvals
  exact hvals

theorem canonicalEvenTrivialBranchTrackingColor1Arithmetic_all
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ z : VZ m, trivialBranchPrefixFiberTrackingColor1ArithmeticAt m z := by
  intro z t ht
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  have hmpos : 0 < m := by
    rcases hm with ⟨hm8, _⟩
    omega
  have hmod :
      ((fiberSum m z.1.val (z.2.1 - fiberIndex z + t).val z.2.2.val : Nat) : ZMod m)
        = (t : ZMod m) := by
    exact canonicalEvenTrivialBranchTrackingColor1ModCore_all m hm z t ht
  have hleftlt :
      fiberSum m z.1.val (z.2.1 - fiberIndex z + t).val z.2.2.val < m := by
    unfold fiberSum
    exact Nat.mod_lt _ hmpos
  have hfiblt : (fiberIndex z).val < m := by
    simpa using (ZMod.val_lt (fiberIndex z))
  have htm : t < m := Nat.lt_trans ht hfiblt
  have hvals :
      (((fiberSum m z.1.val (z.2.1 - fiberIndex z + t).val z.2.2.val : Nat) : ZMod m)).val
        = ((t : ZMod m)).val := by
    exact congrArg ZMod.val hmod
  have hleftval :
      (((fiberSum m z.1.val (z.2.1 - fiberIndex z + t).val z.2.2.val : Nat) : ZMod m)).val
        =
      fiberSum m z.1.val (z.2.1 - fiberIndex z + t).val z.2.2.val := by
    exact ZMod.val_natCast_of_lt hleftlt
  have htval : ((t : ZMod m)).val = t := by
    exact ZMod.val_natCast_of_lt htm
  rw [hleftval, htval] at hvals
  exact hvals

theorem canonicalEvenTrivialBranchTrackingColor2Arithmetic_all
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ z : VZ m, trivialBranchPrefixFiberTrackingColor2ArithmeticAt m z := by
  intro z t ht
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  have hmpos : 0 < m := by
    rcases hm with ⟨hm8, _⟩
    omega
  have hmod :
      ((fiberSum m z.1.val z.2.1.val (z.2.2 - fiberIndex z + t).val : Nat) : ZMod m)
        = (t : ZMod m) := by
    exact canonicalEvenTrivialBranchTrackingColor2ModCore_all m hm z t ht
  have hleftlt :
      fiberSum m z.1.val z.2.1.val (z.2.2 - fiberIndex z + t).val < m := by
    unfold fiberSum
    exact Nat.mod_lt _ hmpos
  have hfiblt : (fiberIndex z).val < m := by
    simpa using (ZMod.val_lt (fiberIndex z))
  have htm : t < m := Nat.lt_trans ht hfiblt
  have hvals :
      (((fiberSum m z.1.val z.2.1.val (z.2.2 - fiberIndex z + t).val : Nat) : ZMod m)).val
        = ((t : ZMod m)).val := by
    exact congrArg ZMod.val hmod
  have hleftval :
      (((fiberSum m z.1.val z.2.1.val (z.2.2 - fiberIndex z + t).val : Nat) : ZMod m)).val
        =
      fiberSum m z.1.val z.2.1.val (z.2.2 - fiberIndex z + t).val := by
    exact ZMod.val_natCast_of_lt hleftlt
  have htval : ((t : ZMod m)).val = t := by
    exact ZMod.val_natCast_of_lt htm
  rw [hleftval, htval] at hvals
  exact hvals

theorem canonicalEvenTrivialBranchTrackingColor0At_all
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ z : VZ m, trivialBranchPrefixFiberTrackingColor0At m z := by
  intro z
  exact trivialBranchPrefixFiberTrackingColor0At_of_arithmetic
    m z
    (canonicalEvenTrivialBranchTrackingColor0Arithmetic_all m hm z)

theorem canonicalEvenTrivialBranchTrackingColor1At_all
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ z : VZ m, trivialBranchPrefixFiberTrackingColor1At m z := by
  intro z
  exact trivialBranchPrefixFiberTrackingColor1At_of_arithmetic
    m z
    (canonicalEvenTrivialBranchTrackingColor1Arithmetic_all m hm z)

theorem canonicalEvenTrivialBranchTrackingColor2At_all
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ z : VZ m, trivialBranchPrefixFiberTrackingColor2At m z := by
  intro z
  exact trivialBranchPrefixFiberTrackingColor2At_of_arithmetic
    m z
    (canonicalEvenTrivialBranchTrackingColor2Arithmetic_all m hm z)

theorem canonicalEvenTrivialBranchTracking_allColors_unbounded
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ c : Color, ∀ z : VZ m,
      trivialBranchPrefixFiberTrackingAt m c z := by
  intro c z
  exact trivialBranchPrefixFiberTrackingAt_of_colorCases
    m c z
    (canonicalEvenTrivialBranchTrackingColor0At_all m hm z)
    (canonicalEvenTrivialBranchTrackingColor1At_all m hm z)
    (canonicalEvenTrivialBranchTrackingColor2At_all m hm z)

theorem canonicalEvenTrivialBranchTrackingColorCases_of_modCoreColor0
    (m : Nat) (hm : admissibleEvenM m)
    (h0 : CanonicalEvenTrivialBranchTrackingColor0ModCore m)
    (h1 :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchPrefixFiberTrackingColor1ArithmeticAt m z)
    (h2 :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchPrefixFiberTrackingColor2ArithmeticAt m z) :
    CanonicalEvenTrivialBranchTrackingColorCases m := by
  apply canonicalEvenTrivialBranchTrackingColorCases_of_separateTargets
  · exact canonicalEvenTrivialBranchTrackingColor0Target_of_modCore m hm h0
  · exact h1
  · exact h2

theorem canonicalEvenTrivialBranchTrackingColorCases_of_modCoreColor0Color1
    (m : Nat) (hm : admissibleEvenM m)
    (h0 : CanonicalEvenTrivialBranchTrackingColor0ModCore m)
    (h1 : CanonicalEvenTrivialBranchTrackingColor1ModCore m)
    (h2 : CanonicalEvenTrivialBranchTrackingColor2ModCore m) :
    CanonicalEvenTrivialBranchTrackingColorCases m := by
  apply canonicalEvenTrivialBranchTrackingColorCases_of_separateTargets
  · exact canonicalEvenTrivialBranchTrackingColor0Target_of_modCore m hm h0
  · exact canonicalEvenTrivialBranchTrackingColor1Target_of_modCore m hm h1
  · exact canonicalEvenTrivialBranchTrackingColor2Target_of_modCore m hm h2

theorem canonicalEvenTrivialBranchTrackingColorCases_all
    (m : Nat) (hm : admissibleEvenM m) :
    CanonicalEvenTrivialBranchTrackingColorCases m := by
  exact canonicalEvenTrivialBranchTrackingColorCases_of_modCoreColor0Color1
    m hm
    (canonicalEvenTrivialBranchTrackingColor0ModCore_all m hm)
    (canonicalEvenTrivialBranchTrackingColor1ModCore_all m hm)
    (canonicalEvenTrivialBranchTrackingColor2ModCore_all m hm)

theorem canonicalEvenTrivialBranchTargetBound_of_vertexFiberSum
    (m : Nat) (hm : admissibleEvenM m)
    {z : VZ m}
    (hz : vertexFiberSum m z ≤ m - 3) :
    trivialBranchTargetBoundAt m z := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  rcases z with ⟨i, j, k⟩
  change (i + j + k : ZMod m).val ≤ m - 3
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
  have hsumlt : fiberSum m i.val j.val k.val < m := by
    unfold fiberSum
    exact Nat.mod_lt _ hmpos
  have hval :
      (i + j + k : ZMod m).val = fiberSum m i.val j.val k.val := by
    have hvals :
        ((((fiberSum m i.val j.val k.val : Nat) : ZMod m)).val)
          = (i + j + k : ZMod m).val := by
      exact congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt hsumlt] at hvals
    exact hvals.symm
  rw [hval]
  simpa [vertexFiberSum] using hz

theorem canonicalEvenTrivialBranchArithmeticTargets_all
    (m : Nat) (hm : admissibleEvenM m) :
    CanonicalEvenTrivialBranchArithmeticTargets m := by
  apply canonicalEvenTrivialBranchArithmeticTargets_of_bound_and_colorCases
  · intro z hz
    exact canonicalEvenTrivialBranchTargetBound_of_vertexFiberSum m hm hz
  · exact canonicalEvenTrivialBranchTrackingColorCases_all m hm

theorem canonicalEvenTrivialBranchCoincidenceAllColors_all
    (m : Nat) (hm : admissibleEvenM m) :
    CanonicalEvenTrivialBranchCoincidenceAllColors m := by
  exact canonicalEvenTrivialBranchCoincidenceAllColors_of_arithmeticTargets
    m hm
    (canonicalEvenTrivialBranchArithmeticTargets_all m hm)

theorem canonicalEvenExceptionalCandidateHitsMSub2AllColors_all
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ c : Color, ∀ z : VZ m,
      vertexFiberSum m z = m - 2 →
      canonicalEvenCandidateHits m c z := by
  exact canonicalEvenExceptionalCandidateHitsMSub2AllColors_of_pure012
    m hm
    (canonicalEvenTrivialBranchCoincidenceAllColors_all m hm)

theorem canonicalEvenExceptionalWitnessesMSub2AllColors_all
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ c : Color, ∀ z : VZ m,
      vertexFiberSum m z = m - 2 →
      CanonicalEvenWitnessAt m c z := by
  exact canonicalEvenExceptionalWitnesses_msub2_allColors_of_candidateHits
    m
    (canonicalEvenExceptionalCandidateHitsMSub2AllColors_all m hm)

/--
Named agreement target for the penultimate vertex on the final exceptional branch `F_{m-1}`.

This identifies the concrete penultimate vertex produced by the canonical even rule
with the corresponding penultimate vertex under the pure `012` dynamics.
-/
def CanonicalEvenExceptionalPenultimateAgreementMSub1AllColors (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m,
    vertexFiberSum m z = m - 1 →
    (residualMapFromFiberZero
      (evenRuleLocalRule m) c (m - 2)
      (canonicalEvenWitnessCandidate m c z)).1
      =
    (residualMapFromFiberZero
      (pure012LocalRule m) c (m - 2)
      (canonicalEvenWitnessCandidate m c z)).1

/--
Named axis-match target for the final exceptional branch `F_{m-1}`.

Once the penultimate vertex has been identified, the only remaining local fact is that
the `tauLayerCode` chosen there selects the same axis as the pure `012` rule for the
active color.
-/
def CanonicalEvenExceptionalTauAxisMatchesPure012MSub1AllColors (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m,
    vertexFiberSum m z = m - 1 →
    axisOfLocalPerm
      (tauLayerCode m
        ((residualMapFromFiberZero
          (evenRuleLocalRule m) c (m - 2)
          (canonicalEvenWitnessCandidate m c z)).1).1.val
        ((residualMapFromFiberZero
          (evenRuleLocalRule m) c (m - 2)
          (canonicalEvenWitnessCandidate m c z)).1).2.1.val) c
      =
    axisOfLocalPerm LocalPerm.p012 c

/--
Pointwise tau-step target on the final exceptional branch `F_{m-1}`.

This is the exact remaining local statement after the trivial branch and the
exceptional branch `F_{m-2}` have been closed:
from the explicit candidate on `F₀`, after `m - 2` steps we reach the penultimate
vertex on `F_{m-2}`, and one final canonical-even successor must land on `z`.
-/
def CanonicalEvenExceptionalTauStepMSub1AllColors (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m,
    vertexFiberSum m z = m - 1 →
    succ (evenRuleLocalRule m) c
      ((residualMapFromFiberZero
        (evenRuleLocalRule m) c (m - 2)
        (canonicalEvenWitnessCandidate m c z)).1) = z

theorem canonicalEvenExceptionalCandidateHitsMSub1AllColors_of_tauStep
    (m : Nat)
    (hstep : CanonicalEvenExceptionalTauStepMSub1AllColors m) :
    CanonicalEvenExceptionalCandidateHitsMSub1AllColors m := by
  intro c z hz
  unfold canonicalEvenCandidateHits
  rw [residualMapFromFiberZero_succ]
  exact hstep c z hz

theorem canonicalEvenExceptionalWitnessesMSub1AllColors_of_tauStep
    (m : Nat)
    (hstep : CanonicalEvenExceptionalTauStepMSub1AllColors m) :
    ∀ c : Color, ∀ z : VZ m,
      vertexFiberSum m z = m - 1 →
      CanonicalEvenWitnessAt m c z := by
  exact canonicalEvenExceptionalWitnesses_msub1_allColors_of_candidateHits
    m
    (canonicalEvenExceptionalCandidateHitsMSub1AllColors_of_tauStep m hstep)

theorem canonicalEvenCompletionTargets_of_tauStepMSub1
    (m : Nat) (hm : admissibleEvenM m)
    (hstep : CanonicalEvenExceptionalTauStepMSub1AllColors m) :
    CanonicalEvenCompletionTargets m := by
  refine ⟨canonicalEvenTrivialBranchCoincidenceAllColors_all m hm, ?_⟩
  refine ⟨canonicalEvenExceptionalWitnessesMSub2AllColors_all m hm, ?_⟩
  exact canonicalEvenExceptionalWitnessesMSub1AllColors_of_tauStep m hstep

theorem canonicalEvenExceptionalPenultimateAgreementMSub1AllColors_all
    (m : Nat) (hm : admissibleEvenM m) :
    CanonicalEvenExceptionalPenultimateAgreementMSub1AllColors m := by
  intro c z hz
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  have hzlt : vertexFiberSum m z < m := by
    exact vertexFiberSum_lt m z
  have hzfib :
      (((vertexFiberSum m z : Nat) : ZMod m)) = fiberIndex z := by
    exact vertexFiberSum_modEq_fiberIndex m z
  have hs :
      (fiberIndex z).val = m - 1 := by
    apply Nat.eq_of_lt_of_lt hzlt
    · simpa [hzfib] using congrArg ZMod.val hzfib
    · omega
  have htriv :
      trivialBranchPure012CoincidesAt m c z := by
    exact canonicalEvenTrivialBranchCoincidenceAllColors_all m hm c z (by omega)
  exact htriv.2 (by simpa [hs])

theorem canonicalEvenExceptionalTauAxisMatchesPure012MSub1AllColors_all
    (m : Nat) (hm : admissibleEvenM m) :
    CanonicalEvenExceptionalTauAxisMatchesPure012MSub1AllColors m := by
  intro c z hz
  let v :=
    (residualMapFromFiberZero
      (evenRuleLocalRule m) c (m - 2)
      (canonicalEvenWitnessCandidate m c z)).1
  have hm8 : 8 ≤ m := hm.1
  have hsum : vertexFiberSum m v ≤ m - 3 := by
    have hvfib :
        fiberIndex v = (fiberIndex ((canonicalEvenWitnessCandidate m c z).1) + ((m - 2) : ZMod m)) := by
      simpa [v] using fiberIndex_residualMapFromFiberZero
        (σ := evenRuleLocalRule m) (c := c) (k := m - 2)
        (x := canonicalEvenWitnessCandidate m c z)
    have hx0 : fiberIndex ((canonicalEvenWitnessCandidate m c z).1) = 0 := by
      exact (canonicalEvenWitnessCandidate_mem m c z)
    have hv :
        fiberIndex v = ((m - 2 : Nat) : ZMod m) := by
      simpa [hx0] using hvfib
    have hvval : (fiberIndex v).val = m - 2 := by
      have hmpos : 0 < m := by omega
      have hlt : m - 2 < m := by omega
      apply ZMod.natCast_zmod_eq_iff_dvd.mp
      rw [ZMod.natCast_val]
      exact dvd_refl m
    have hvsum :
        vertexFiberSum m v = m - 2 := by
      exact vertexFiberSum_eq_of_fiberIndex_val m v hvval
    omega
  have hfalse :
      residualSupport m v.1.val v.2.1.val v.2.2.val = false := by
    exact residualSupport_false_of_le_msub3
      (m := m) (i := v.1.val) (j := v.2.1.val) (k := v.2.2.val) hm8
    rw [hsum]
    omega
  have hconcrete :
      evenRuleLocalRule m v c = axisOfLocalPerm LocalPerm.p012 c := by
    exact evenRuleLocalRule_of_not_residualSupport m v hm c hfalse
  have hpure :
      pure012LocalRule m v c = axisOfLocalPerm LocalPerm.p012 c := by
    simp [pure012LocalRule]
  exact hconcrete.trans hpure.symm

theorem canonicalEvenExceptionalTauStepMSub1AllColors_of_agreement_and_axisMatch
    (m : Nat) (hm : admissibleEvenM m)
    (hag : CanonicalEvenExceptionalPenultimateAgreementMSub1AllColors m)
    (haxis : CanonicalEvenExceptionalTauAxisMatchesPure012MSub1AllColors m) :
    CanonicalEvenExceptionalTauStepMSub1AllColors m := by
  intro c z hz
  let wc :=
    (residualMapFromFiberZero
      (evenRuleLocalRule m) c (m - 2)
      (canonicalEvenWitnessCandidate m c z)).1
  let wp :=
    (residualMapFromFiberZero
      (pure012LocalRule m) c (m - 2)
      (canonicalEvenWitnessCandidate m c z)).1
  have hw : wc = wp := by
    simpa [wc, wp] using hag c z hz
  have hax :
      axisOfLocalPerm (tauLayerCode m wc.1.val wc.2.1.val) c =
        axisOfLocalPerm LocalPerm.p012 c := by
    simpa [wc] using haxis c z hz
  have hpure :
      succ (pure012LocalRule m) c wp = z := by
    exact pure012ExceptionalPenultimateMSub1AllColors_all m hm c z hz
  change bump (axisOfLocalPerm (tauLayerCode m wc.1.val wc.2.1.val) c) wc = z
  rw [hax, hw]
  simpa [succ, pure012LocalRule] using hpure

theorem canonicalEvenCompletionTargets_of_agreement_and_tauAxisMSub1
    (m : Nat) (hm : admissibleEvenM m)
    (hag : CanonicalEvenExceptionalPenultimateAgreementMSub1AllColors m)
    (haxis : CanonicalEvenExceptionalTauAxisMatchesPure012MSub1AllColors m) :
    CanonicalEvenCompletionTargets m := by
  exact canonicalEvenCompletionTargets_of_tauStepMSub1
    m hm
    (canonicalEvenExceptionalTauStepMSub1AllColors_of_agreement_and_axisMatch
      m hm hag haxis)

/--
Correct final witness route for the `F_{m-1}` branch.

Instead of requiring a global tau-vs-`012` axis match at the penultimate vertex,
it is enough to exhibit, for each `z ∈ F_{m-1}`, a predecessor `w ∈ F_{m-2}`
that already has a canonical-even witness and whose final concrete successor is `z`.
-/
def CanonicalEvenExceptionalTauPredecessorWitnessMSub1AllColors (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m,
    vertexFiberSum m z = m - 1 →
    ∃ w : VZ m,
      vertexFiberSum m w = m - 2 ∧
      succ (evenRuleLocalRule m) c w = z ∧
      CanonicalEvenWitnessAt m c w

theorem canonicalEvenExceptionalWitnessAt_msub1_of_tauPredecessor
    (m : Nat) (hm : admissibleEvenM m)
    {c : Color} {z w : VZ m}
    (hz : vertexFiberSum m z = m - 1)
    (hw : vertexFiberSum m w = m - 2)
    (hstep : succ (evenRuleLocalRule m) c w = z)
    (hwit : CanonicalEvenWitnessAt m c w) :
    CanonicalEvenWitnessAt m c z := by
  rcases hwit with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  have hzfib : (fiberIndex z).val = m - 1 := by
    rw [fiberIndex_val_eq_vertexFiberSum m hm z, hz]
  have hwfib : (fiberIndex w).val = m - 2 := by
    rw [fiberIndex_val_eq_vertexFiberSum m hm w, hw]
  have hmsub : m - 1 = (m - 2) + 1 := by
    rcases hm with ⟨hm8, _⟩
    omega
  rw [residualMapFromFiberZero_val, hzfib, hmsub, succPow_succ]
  have hy' : succPow (evenRuleLocalRule m) c (m - 2) y.1 = w := by
    rw [hwfib] at hy
    simpa [residualMapFromFiberZero_val] using hy
  simpa [hy', hstep]

theorem canonicalEvenExceptionalWitnesses_msub1_allColors_of_tauPredecessor
    (m : Nat) (hm : admissibleEvenM m)
    (hpred : CanonicalEvenExceptionalTauPredecessorWitnessMSub1AllColors m) :
    ∀ c : Color, ∀ z : VZ m,
      vertexFiberSum m z = m - 1 →
      CanonicalEvenWitnessAt m c z := by
  intro c z hz
  rcases hpred c z hz with ⟨w, hw, hstep, hwit⟩
  exact canonicalEvenExceptionalWitnessAt_msub1_of_tauPredecessor
    m hm hz hw hstep hwit

theorem canonicalEvenCompletionTargets_of_tauPredecessorWitnessMSub1
    (m : Nat) (hm : admissibleEvenM m)
    (hpred : CanonicalEvenExceptionalTauPredecessorWitnessMSub1AllColors m) :
    CanonicalEvenCompletionTargets m := by
  exact canonicalEvenCompletionTargets_of_msub1
    m hm
    (canonicalEvenExceptionalWitnesses_msub1_allColors_of_tauPredecessor
      m hm hpred)

/--
Explicit predecessor candidates for the final exceptional branch `F_{m-1}`.

These are the only three possible immediate predecessors of a target vertex `z`:
decrement the `i`, `j`, or `k` coordinate by one.
-/
def canonicalEvenExceptionalTauPredecessorXMSub1 (m : Nat) (z : VZ m) : VZ m :=
  (z.1 - 1, z.2.1, z.2.2)

def canonicalEvenExceptionalTauPredecessorYMSub1 (m : Nat) (z : VZ m) : VZ m :=
  (z.1, z.2.1 - 1, z.2.2)

def canonicalEvenExceptionalTauPredecessorZMSub1 (m : Nat) (z : VZ m) : VZ m :=
  (z.1, z.2.1, z.2.2 - 1)

/--
Explicit chosen predecessor for the final exceptional branch `F_{m-1}`.

We first test the `i`-predecessor, then the `j`-predecessor; if neither already
maps to `z` under the concrete canonical-even successor, the remaining choice is
the `k`-predecessor.
-/
def canonicalEvenExceptionalTauPredecessorMSub1
    (m : Nat) (c : Color) (z : VZ m) : VZ m :=
  let wx := canonicalEvenExceptionalTauPredecessorXMSub1 m z
  let wy := canonicalEvenExceptionalTauPredecessorYMSub1 m z
  let wz := canonicalEvenExceptionalTauPredecessorZMSub1 m z
  if succ (evenRuleLocalRule m) c wx = z then wx
  else if succ (evenRuleLocalRule m) c wy = z then wy
  else wz

/--
Named remaining local target for the explicit predecessor formulation on `F_{m-1}`.

This is the concrete version of the predecessor-witness route:
the chosen predecessor must map to the target vertex in one canonical-even step.
-/
def CanonicalEvenExceptionalTauPredecessorStepMSub1AllColors (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m,
    vertexFiberSum m z = m - 1 →
    succ (evenRuleLocalRule m) c
      (canonicalEvenExceptionalTauPredecessorMSub1 m c z) = z

theorem canonicalEvenExceptionalTauPredecessorWitnessMSub1AllColors_of_explicitStep
    (m : Nat) (hm : admissibleEvenM m)
    (hstep : CanonicalEvenExceptionalTauPredecessorStepMSub1AllColors m) :
    CanonicalEvenExceptionalTauPredecessorWitnessMSub1AllColors m := by
  intro c z hz
  refine ⟨canonicalEvenExceptionalTauPredecessorMSub1 m c z, ?_, ?_, ?_⟩
  · let w := canonicalEvenExceptionalTauPredecessorMSub1 m c z
    have hstepw : succ (evenRuleLocalRule m) c w = z := by
      simpa [w] using hstep c z hz
    have hzfib : (fiberIndex z).val = m - 1 := by
      rw [fiberIndex_val_eq_vertexFiberSum m hm z, hz]
    have hzmod : fiberIndex z = ((m - 1 : Nat) : ZMod m) := by
      rw [← ZMod.natCast_val (fiberIndex z), hzfib]
    have hfi0 : fiberIndex z = fiberIndex w + 1 := by
      simpa [w, hstepw] using
        (fiberIndex_succ (σ := evenRuleLocalRule m) (c := c) w)
    have hcast1 :
        (((m - 2 : Nat) : ZMod m) + 1 : ZMod m) = ((m - 1 : Nat) : ZMod m) := by
      rw [show m - 1 = (m - 2) + 1 by
            rcases hm with ⟨hm8, _⟩
            omega, Nat.cast_add]
      simp
    have hfi :
        fiberIndex w + 1 = (((m - 2 : Nat) : ZMod m) + 1 : ZMod m) := by
      calc
        fiberIndex w + 1 = fiberIndex z := by
          symm
          exact hfi0
        _ = ((m - 1 : Nat) : ZMod m) := hzmod
        _ = (((m - 2 : Nat) : ZMod m) + 1 : ZMod m) := by
          simpa using hcast1.symm
    have hwmod : fiberIndex w = ((m - 2 : Nat) : ZMod m) := by
      exact add_right_cancel hfi
    have hlt : m - 2 < m := by
      rcases hm with ⟨hm8, _⟩
      omega
    have hwval : (fiberIndex w).val = m - 2 := by
      have hvals :
          (fiberIndex w).val = (((m - 2 : Nat) : ZMod m)).val := by
        exact congrArg ZMod.val hwmod
      simpa [ZMod.val_natCast_of_lt hlt] using hvals
    rw [← fiberIndex_val_eq_vertexFiberSum m hm w]
    exact hwval
  · exact hstep c z hz
  · exact canonicalEvenExceptionalWitnesses_msub2_allColors
      m hm c
      (canonicalEvenExceptionalTauPredecessorMSub1 m c z)
      (by
        let w := canonicalEvenExceptionalTauPredecessorMSub1 m c z
        have hstepw : succ (evenRuleLocalRule m) c w = z := by
          simpa [w] using hstep c z hz
        have hzfib : (fiberIndex z).val = m - 1 := by
          rw [fiberIndex_val_eq_vertexFiberSum m hm z, hz]
        have hzmod : fiberIndex z = ((m - 1 : Nat) : ZMod m) := by
          rw [← ZMod.natCast_val (fiberIndex z), hzfib]
        have hfi0 : fiberIndex z = fiberIndex w + 1 := by
          simpa [w, hstepw] using
            (fiberIndex_succ (σ := evenRuleLocalRule m) (c := c) w)
        have hcast1 :
            (((m - 2 : Nat) : ZMod m) + 1 : ZMod m) = ((m - 1 : Nat) : ZMod m) := by
          rw [show m - 1 = (m - 2) + 1 by
                rcases hm with ⟨hm8, _⟩
                omega, Nat.cast_add]
          simp
        have hfi :
            fiberIndex w + 1 = (((m - 2 : Nat) : ZMod m) + 1 : ZMod m) := by
          calc
            fiberIndex w + 1 = fiberIndex z := by
              symm
              exact hfi0
            _ = ((m - 1 : Nat) : ZMod m) := hzmod
            _ = (((m - 2 : Nat) : ZMod m) + 1 : ZMod m) := by
              simpa using hcast1.symm
        have hwmod : fiberIndex w = ((m - 2 : Nat) : ZMod m) := by
          exact add_right_cancel hfi
        have hlt : m - 2 < m := by
          rcases hm with ⟨hm8, _⟩
          omega
        have hwval : (fiberIndex w).val = m - 2 := by
          have hvals :
              (fiberIndex w).val = (((m - 2 : Nat) : ZMod m)).val := by
            exact congrArg ZMod.val hwmod
          simpa [ZMod.val_natCast_of_lt hlt] using hvals
        rw [← fiberIndex_val_eq_vertexFiberSum m hm w]
        exact hwval)

theorem canonicalEvenCompletionTargets_of_explicitTauPredecessorStepMSub1
    (m : Nat) (hm : admissibleEvenM m)
    (hstep : CanonicalEvenExceptionalTauPredecessorStepMSub1AllColors m) :
    CanonicalEvenCompletionTargets m := by
  exact canonicalEvenCompletionTargets_of_tauPredecessorWitnessMSub1
    m hm
    (canonicalEvenExceptionalTauPredecessorWitnessMSub1AllColors_of_explicitStep
      m hm hstep)

end ClaudeCyclesARZN
