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

theorem canonicalEvenCompletionTargets_of_exceptionalWitnesses
    (m : Nat) (hm : admissibleEvenM m)
    (hexc : CanonicalEvenExceptionalWitnessesAllColors m) :
    CanonicalEvenCompletionTargets m := by
  exact ⟨canonicalEvenTrivialBranchCoincidenceAllColors_all m hm, hexc⟩

theorem canonicalEvenCompletionTargets_all_of_exceptionalWitnesses
    (m : Nat) (hm : admissibleEvenM m)
    (hsub2 :
      ∀ c : Color, ∀ z : VZ m,
        vertexFiberSum m z = m - 2 →
        CanonicalEvenWitnessAt m c z)
    (hsub1 :
      ∀ c : Color, ∀ z : VZ m,
        vertexFiberSum m z = m - 1 →
        CanonicalEvenWitnessAt m c z) :
    CanonicalEvenCompletionTargets m := by
  refine ⟨canonicalEvenTrivialBranchCoincidenceAllColors_all m hm, ?_⟩
  exact ⟨hsub2, hsub1⟩

theorem fiberIndex_val_eq_vertexFiberSum
    (m : Nat) (hm : admissibleEvenM m) (z : VZ m) :
    (fiberIndex z).val = vertexFiberSum m z := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  rcases z with ⟨i, j, k⟩
  change (i + j + k : ZMod m).val = fiberSum m i.val j.val k.val
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
  rw [ZMod.val_natCast_of_lt hlt] at hvals
  exact hvals.symm

theorem trivialBranchPrefixOutsideResidualAt_of_tracking_eq_msub2
    (m : Nat) (c : Color) (z : VZ m)
    (hm : admissibleEvenM m)
    (hz : vertexFiberSum m z = m - 2)
    (htrack : trivialBranchPrefixFiberTrackingAt m c z) :
    trivialBranchPrefixOutsideResidualAt m c z := by
  intro t ht
  let v := succPow (pure012LocalRule m) c t (canonicalEvenWitnessCandidate m c z).1
  have hm8 : 8 ≤ m := hm.1
  have hfib : (fiberIndex z).val = vertexFiberSum m z := by
    exact fiberIndex_val_eq_vertexFiberSum m hm z
  have hsub2fib : (fiberIndex z).val = m - 2 := by
    rw [hfib, hz]
  have htle : t ≤ m - 3 := by
    omega
  have hsum : fiberSum m v.1.val v.2.1.val v.2.2.val = t := by
    simpa [v] using htrack t ht
  apply not_residualSupport_of_le_msub3
    (m := m) (i := v.1.val) (j := v.2.1.val) (k := v.2.2.val) hm8
  rw [hsum]
  exact htle

theorem canonicalEvenExceptionalWitnesses_msub2_allColors
    (m : Nat) (hm : admissibleEvenM m) :
    ∀ c : Color, ∀ z : VZ m,
      vertexFiberSum m z = m - 2 →
      CanonicalEvenWitnessAt m c z := by
  intro c z hz
  have htrack : trivialBranchPrefixFiberTrackingAt m c z := by
    exact canonicalEvenTrivialBranchTracking_allColors_unbounded m hm c z
  have hout : trivialBranchPrefixOutsideResidualAt m c z := by
    exact trivialBranchPrefixOutsideResidualAt_of_tracking_eq_msub2
      m c z hm hz htrack
  have hprefix : trivialBranchPrefixAgreementAt m c z := by
    exact trivialBranchPrefixAgreementAt_of_outsideResidual
      m c z hm hout
  have hcoinc : trivialBranchPure012CoincidesAt m c z := by
    exact trivialBranchPure012CoincidesAt_of_prefixAgreement
      m c z hprefix
  exact canonicalEvenWitnessAt_of_trivialBranchPure012Coincides
    m c hm z hcoinc

theorem canonicalEvenExceptionalWitnesses_all_of_msub1
    (m : Nat) (hm : admissibleEvenM m)
    (hsub1 :
      ∀ c : Color, ∀ z : VZ m,
        vertexFiberSum m z = m - 1 →
        CanonicalEvenWitnessAt m c z) :
    CanonicalEvenExceptionalWitnessesAllColors m := by
  exact ⟨canonicalEvenExceptionalWitnesses_msub2_allColors m hm, hsub1⟩

theorem canonicalEvenCompletionTargets_of_msub1
    (m : Nat) (hm : admissibleEvenM m)
    (hsub1 :
      ∀ c : Color, ∀ z : VZ m,
        vertexFiberSum m z = m - 1 →
        CanonicalEvenWitnessAt m c z) :
    CanonicalEvenCompletionTargets m := by
  exact canonicalEvenCompletionTargets_of_exceptionalWitnesses
    m hm
    (canonicalEvenExceptionalWitnesses_all_of_msub1 m hm hsub1)

/--
Named penultimate-step target for the final exceptional branch `F_{m-1}`.

For a target vertex `z ∈ F_{m-1}`, after `m - 2` concrete successor steps
from the explicit candidate on `F₀`, it remains only to verify that one final
successor step lands exactly on `z`.
-/
def CanonicalEvenExceptionalPenultimateMSub1AllColors (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m,
    vertexFiberSum m z = m - 1 →
    succ (evenRuleLocalRule m) c
      ((residualMapFromFiberZero
        (evenRuleLocalRule m) c (m - 2)
        (canonicalEvenWitnessCandidate m c z)).1) = z

theorem canonicalEvenExceptionalCandidateHits_msub1_allColors_of_penultimate
    (m : Nat) (hm : admissibleEvenM m)
    (hpen : CanonicalEvenExceptionalPenultimateMSub1AllColors m) :
    CanonicalEvenExceptionalCandidateHitsMSub1AllColors m := by
  intro c z hz
  unfold canonicalEvenCandidateHits
  have hfib : (fiberIndex z).val = m - 1 := by
    rw [fiberIndex_val_eq_vertexFiberSum m hm z, hz]
  have hmsub : m - 1 = (m - 2) + 1 := by
    rcases hm with ⟨hm8, _⟩
    omega
  rw [hfib, hmsub, residualMapFromFiberZero_val, succPow_succ]
  simpa [residualMapFromFiberZero_val] using hpen c z hz

theorem canonicalEvenExceptionalWitnesses_msub1_allColors_of_penultimate
    (m : Nat) (hm : admissibleEvenM m)
    (hpen : CanonicalEvenExceptionalPenultimateMSub1AllColors m) :
    ∀ c : Color, ∀ z : VZ m,
      vertexFiberSum m z = m - 1 →
      CanonicalEvenWitnessAt m c z := by
  exact canonicalEvenExceptionalWitnesses_msub1_allColors_of_candidateHits
    m
    (canonicalEvenExceptionalCandidateHits_msub1_allColors_of_penultimate m hm hpen)

theorem canonicalEvenCompletionTargets_of_penultimateMSub1
    (m : Nat) (hm : admissibleEvenM m)
    (hpen : CanonicalEvenExceptionalPenultimateMSub1AllColors m) :
    CanonicalEvenCompletionTargets m := by
  exact canonicalEvenCompletionTargets_of_msub1
    m hm
    (canonicalEvenExceptionalWitnesses_msub1_allColors_of_penultimate m hm hpen)

/--
Named final local target for the `F_{m-1}` branch.

At the penultimate vertex reached after `m - 2` concrete successor steps from the
explicit candidate, the only remaining work is to show that the local rule on
`F_{m-2}` selects the tau-layer axis that bumps exactly to the target `z ∈ F_{m-1}`.
-/
def CanonicalEvenExceptionalTauStepMSub1AllColors (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m,
    vertexFiberSum m z = m - 1 →
    let w :=
      (residualMapFromFiberZero
        (evenRuleLocalRule m) c (m - 2)
        (canonicalEvenWitnessCandidate m c z)).1
    bump (axisOfLocalPerm (tauLayerCode m w.1.val w.2.1.val) c) w = z

theorem canonicalEvenExceptionalPenultimateVertex_msub2
    (m : Nat) (hm : admissibleEvenM m) (c : Color) (z : VZ m) :
    vertexFiberSum m
      ((residualMapFromFiberZero
        (evenRuleLocalRule m) c (m - 2)
        (canonicalEvenWitnessCandidate m c z)).1) = m - 2 := by
  letI : NeZero m := neZero_of_admissibleEvenM m hm
  let w :=
    (residualMapFromFiberZero
      (evenRuleLocalRule m) c (m - 2)
      (canonicalEvenWitnessCandidate m c z)).1
  have hmem0 : (canonicalEvenWitnessCandidate m c z).1 ∈ Fiber m 0 := by
    exact canonicalEvenWitnessCandidate_mem m c z
  have hmem : w ∈ Fiber m ((m - 2 : Nat) : ZMod m) := by
    simpa [w, residualMapFromFiberZero_val] using
      (succPow_maps_fiber
        (σ := evenRuleLocalRule m) (c := c) (n := m - 2)
        (s := (0 : ZMod m)) hmem0)
  have hmod : fiberIndex w = ((m - 2 : Nat) : ZMod m) := by
    simpa [Fiber] using hmem
  have hcast : (((m - 2 : Nat) : ZMod m)).val = m - 2 := by
    rcases hm with ⟨hm8, _⟩
    exact ZMod.val_natCast_of_lt (by omega)
  have hval : (fiberIndex w).val = m - 2 := by
    have hvals : (fiberIndex w).val = (((m - 2 : Nat) : ZMod m)).val := by
      exact congrArg ZMod.val hmod
    simpa [hcast] using hvals
  rw [← fiberIndex_val_eq_vertexFiberSum m hm w]
  exact hval

theorem canonicalEvenExceptionalPenultimateMSub1AllColors_of_tauStep
    (m : Nat) (hm : admissibleEvenM m)
    (htau : CanonicalEvenExceptionalTauStepMSub1AllColors m) :
    CanonicalEvenExceptionalPenultimateMSub1AllColors m := by
  intro c z hz
  let w :=
    (residualMapFromFiberZero
      (evenRuleLocalRule m) c (m - 2)
      (canonicalEvenWitnessCandidate m c z)).1
  have hw : vertexFiberSum m w = m - 2 := by
    simpa [w] using canonicalEvenExceptionalPenultimateVertex_msub2 m hm c z
  have hloc :
      evenRuleLocalRule m w c =
        axisOfLocalPerm (tauLayerCode m w.1.val w.2.1.val) c := by
    exact evenRuleLocalRule_of_eq_msub2 m w hm c hw
  change succ (evenRuleLocalRule m) c w = z
  unfold succ
  rw [hloc]
  simpa [w] using htau c z hz

theorem canonicalEvenCompletionTargets_of_tauStepMSub1
    (m : Nat) (hm : admissibleEvenM m)
    (htau : CanonicalEvenExceptionalTauStepMSub1AllColors m) :
    CanonicalEvenCompletionTargets m := by
  exact canonicalEvenCompletionTargets_of_penultimateMSub1
    m hm
    (canonicalEvenExceptionalPenultimateMSub1AllColors_of_tauStep m hm htau)

/--
Named agreement target for the penultimate vertex on the final exceptional branch `F_{m-1}`.

Up to time `m - 2`, the concrete residual lift and the pure `012` residual lift
start from the same explicit candidate on `F₀`; this target asks them to agree
on the penultimate vertex.
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
Named local-axis target for the final exceptional branch `F_{m-1}`.

At the concrete penultimate vertex on `F_{m-2}`, the tau-layer axis selected by the
canonical even rule must match the pure `012` axis for the corresponding color.
-/
def CanonicalEvenExceptionalTauAxisMatchesPure012MSub1AllColors (m : Nat) : Prop :=
  ∀ c : Color, ∀ z : VZ m,
    vertexFiberSum m z = m - 1 →
    let w :=
      (residualMapFromFiberZero
        (evenRuleLocalRule m) c (m - 2)
        (canonicalEvenWitnessCandidate m c z)).1
    axisOfLocalPerm (tauLayerCode m w.1.val w.2.1.val) c =
      axisOfLocalPerm LocalPerm.p012 c

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

end ClaudeCyclesARZN
