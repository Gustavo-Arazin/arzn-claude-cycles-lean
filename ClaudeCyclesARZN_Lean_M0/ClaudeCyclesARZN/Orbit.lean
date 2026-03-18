import ClaudeCyclesARZN.Reduction
import Mathlib

namespace ClaudeCyclesARZN

/-- Iteration is additive in the number of successor steps. -/
theorem succPow_add {m : Nat} (σ : LocalRule m) (c : Color) (a b : Nat) (v : VZ m) :
    succPow σ c (a + b) v = succPow σ c b (succPow σ c a v) := by
  induction b generalizing v with
  | zero =>
      simp [succPow]
  | succ b ih =>
      simp [Nat.add_assoc, succPow, ih]

/-- Decomposition of an iterate into a block of size `k*m` plus a remainder `r`. -/
theorem succPow_mul_add {m : Nat} (σ : LocalRule m) (c : Color) (k r : Nat) (v : VZ m) :
    succPow σ c (k * m + r) v = succPow σ c r (succPow σ c (k * m) v) := by
  simpa using succPow_add (σ := σ) (c := c) (a := k * m) (b := r) v

/-- Starting from the reference fiber `F_0`, after `r` steps the orbit lies in `F_r`. -/
theorem succPow_from_fiberZero {m : Nat} (σ : LocalRule m) (c : Color) (r : Nat)
    {v : VZ m} (hv : v ∈ Fiber m 0) :
    succPow σ c r v ∈ Fiber m (r : ZMod m) := by
  have h := succPow_maps_fiber (σ := σ) (c := c) (n := r) (s := (0 : ZMod m)) hv
  simpa using h

/-- Starting from `F_0`, an iterate of the form `k*m + r` lands in the fiber `F_r`. -/
theorem succPow_mul_add_from_fiberZero {m : Nat} (σ : LocalRule m) (c : Color) (k r : Nat)
    {v : VZ m} (hv : v ∈ Fiber m 0) :
    succPow σ c (k * m + r) v ∈ Fiber m (r : ZMod m) := by
  have h := succPow_maps_fiber (σ := σ) (c := c) (n := k * m + r) (s := (0 : ZMod m)) hv
  simpa [Nat.cast_add, Nat.cast_mul, add_assoc] using h

end ClaudeCyclesARZN
