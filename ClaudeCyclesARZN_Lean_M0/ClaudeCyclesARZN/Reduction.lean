import ClaudeCyclesARZN.ReturnMap
import Mathlib

namespace ClaudeCyclesARZN

/-- The distinguished reference fiber `F_0`, as a subtype. -/
abbrev FiberZero (m : Nat) : Type := {v : VZ m // v ∈ Fiber m 0}

/-- The return map restricted to the reference fiber `F_0`. -/
def returnMapOnFiberZero {m : Nat} (σ : LocalRule m) (c : Color) :
    FiberZero m → FiberZero m
  | ⟨v, hv⟩ =>
      ⟨returnMap σ c v, by
        have h := returnMap_preserves_fiber (σ := σ) (c := c) (s := (0 : ZMod m)) hv
        simpa using h⟩

@[simp] theorem returnMapOnFiberZero_val {m : Nat} (σ : LocalRule m) (c : Color)
    (x : FiberZero m) :
    (returnMapOnFiberZero σ c x).1 = returnMap σ c x.1 := rfl

/-- After a multiple of `m` steps, every vertex returns to its original fiber. -/
theorem succPow_mul_m_preserves_fiber {m : Nat} (σ : LocalRule m) (c : Color) (k : Nat)
    {s : ZMod m} {v : VZ m} (hv : v ∈ Fiber m s) :
    succPow σ c (k * m) v ∈ Fiber m s := by
  have h :=
    succPow_maps_fiber (σ := σ) (c := c) (n := k * m) (s := s) hv
  simpa [Nat.cast_mul, add_assoc] using h

/-- In particular, the iterate `φ_c^(k*m)` preserves the reference fiber `F_0`. -/
theorem succPow_mul_m_preserves_fiberZero {m : Nat} (σ : LocalRule m) (c : Color) (k : Nat)
    {v : VZ m} (hv : v ∈ Fiber m 0) :
    succPow σ c (k * m) v ∈ Fiber m 0 := by
  exact succPow_mul_m_preserves_fiber (σ := σ) (c := c) (k := k) hv

/-
M2 target not yet formalized in compiled form:

If `returnMapOnFiberZero σ c` is a single cycle on `FiberZero m`,
then `succ σ c` is a single cycle on the full vertex set `VZ m`.

This stronger global-to-fiber reduction lemma is the next step (M2b).
-/

end ClaudeCyclesARZN
