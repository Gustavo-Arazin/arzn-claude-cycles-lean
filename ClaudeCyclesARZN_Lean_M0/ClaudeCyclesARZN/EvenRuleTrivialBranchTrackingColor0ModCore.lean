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
    (h2 :
      ∀ z : VZ m,
        vertexFiberSum m z ≤ m - 3 →
        trivialBranchPrefixFiberTrackingColor2ArithmeticAt m z) :
    CanonicalEvenTrivialBranchTrackingColorCases m := by
  apply canonicalEvenTrivialBranchTrackingColorCases_of_separateTargets
  · exact canonicalEvenTrivialBranchTrackingColor0Target_of_modCore m hm h0
  · exact canonicalEvenTrivialBranchTrackingColor1Target_of_modCore m hm h1
  · exact h2

theorem canonicalEvenTrivialBranchTrackingColorCases_of_modCoreColor0Color1Color2
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
  exact canonicalEvenTrivialBranchTrackingColorCases_of_modCoreColor0Color1Color2
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

theorem canonicalEvenTrivialBranchTrackingColor0Arithmetic_all
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ z : VZ m, trivialBranchPrefixFiberTrackingColor0ArithmeticAt m z := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  intro z t ht
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
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  intro z t ht
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
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  intro z t ht
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

theorem trivialBranchPrefixOutsideResidualAt_of_tracking_and_eq_msub2
    (m : Nat) (c : Color) (z : VZ m)
    (hm : admissibleEvenM m)
    (hz : vertexFiberSum m z = m - 2)
    (htrack : trivialBranchPrefixFiberTrackingAt m c z) :
    trivialBranchPrefixOutsideResidualAt m c z := by
intro t ht
letI : NeZero m := neZero_of_admissibleEvenM m hm  
let v := succPow (pure012LocalRule m) c t (canonicalEvenWitnessCandidate m c z).1
have hm8 : 8 ≤ m := hm.1
have hfib :
    (fiberIndex z).val = vertexFiberSum m z := by
  rcases z with ⟨i, j, k⟩
  change (i + j + k).val = fiberSum m i.val j.val k.val
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
    unfold fiberSum      exact Nat.mod_lt _ hmpos
  have hvals :
      (((fiberSum m i.val j.val k.val : Nat) : ZMod m)).val = (i + j + k).val := by
    exact congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt hlt] at hvals
  exact hvals.symm
have hsub2fib : (fiberIndex z).val = m - 2 := by
  rw [hfib, hz]
have htle : t ≤ m - 3 := by
  omega
have hsum : fiberSum m v.1.val v.2.1.val v.2.2.val = t := by
  simpa [v] using htrack t ht
simpa [v] using
  (not_residualSupport_of_le_msub3
    (m := m) (i := v.1.val) (j := v.2.1.val) (k := v.2.2.val) hm8 (by
      rw [hsum]
      exact htle))

theorem canonicalEvenExceptionalWitnesses_msub2_allColors
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ c : Color, ∀ z : VZ m,
      vertexFiberSum m z = m - 2 →
      CanonicalEvenWitnessAt m c z := by
  intro c z hz
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  have htrack : trivialBranchPrefixFiberTrackingAt m c z := by
    apply trivialBranchPrefixFiberTrackingAt_of_colorCases m c z
    · exact trivialBranchPrefixFiberTrackingColor0At_of_arithmetic
        m z (canonicalEvenTrivialBranchTrackingColor0Arithmetic_all m hm z)
    · exact trivialBranchPrefixFiberTrackingColor1At_of_arithmetic
        m z (canonicalEvenTrivialBranchTrackingColor1Arithmetic_all m hm z)
    · exact trivialBranchPrefixFiberTrackingColor2At_of_arithmetic
        m z (canonicalEvenTrivialBranchTrackingColor2Arithmetic_all m hm z)
  have hout :
      trivialBranchPrefixOutsideResidualAt m c z := by
    exact trivialBranchPrefixOutsideResidualAt_of_tracking_and_eq_msub2
      m c z hm hz htrack
  have hprefix :
      trivialBranchPrefixAgreementAt m c z := by
    exact trivialBranchPrefixAgreementAt_of_outsideResidual
      m c z hm hout
  have hcoinc :
      trivialBranchPure012CoincidesAt m c z := by
    exact trivialBranchPure012CoincidesAt_of_prefixAgreement
      m c z hprefix
  exact canonicalEvenWitnessAt_of_trivialBranchPure012Coincides
    m c hm z hcoinc

end ClaudeCyclesARZN
