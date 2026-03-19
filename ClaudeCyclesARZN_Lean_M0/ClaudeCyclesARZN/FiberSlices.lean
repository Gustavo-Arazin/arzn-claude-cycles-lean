import ClaudeCyclesARZN.ReturnIterates
import Mathlib

namespace ClaudeCyclesARZN

/-- The fiber `F_s` as a subtype. -/
abbrev FiberAt (m : Nat) (s : ZMod m) : Type := {v : VZ m // v ∈ Fiber m s}

/-- Residual evolution from the reference fiber `F_0` into the fiber `F_r`. -/
def residualMapFromFiberZero {m : Nat} (σ : LocalRule m) (c : Color) (r : Nat) :
    FiberZero m → FiberAt m (r : ZMod m)
  | ⟨v, hv⟩ =>
      ⟨succPow σ c r v, succPow_from_fiberZero (σ := σ) (c := c) (r := r) hv⟩

@[simp] theorem residualMapFromFiberZero_val {m : Nat} (σ : LocalRule m) (c : Color)
    (r : Nat) (x : FiberZero m) :
    (residualMapFromFiberZero σ c r x).1 = succPow σ c r x.1 := rfl

/-- Starting from `F_0`, an orbit segment of length `k*m + r`
factors as `k` return steps followed by `r` residual steps. -/
theorem succPow_factor_from_fiberZero {m : Nat} (σ : LocalRule m) (c : Color)
    (k r : Nat) (x : FiberZero m) :
    (residualMapFromFiberZero σ c r (returnPowOnFiberZero σ c k x)).1
      = succPow σ c (k * m + r) x.1 := by
  rw [residualMapFromFiberZero_val]
  rw [returnPowOnFiberZero_val]
  symm
  exact succPow_block_decomposition (σ := σ) (c := c) (k := k) (r := r) x.1

/-- The codomain of the factorization is exactly the expected fiber `F_r`. -/
theorem succPow_factor_from_fiberZero_mem {m : Nat} (σ : LocalRule m) (c : Color)
    (k r : Nat) (x : FiberZero m) :
    succPow σ c (k * m + r) x.1 ∈ Fiber m (r : ZMod m) := by
  have h :=
    (residualMapFromFiberZero σ c r (returnPowOnFiberZero σ c k x)).2
  rw [succPow_factor_from_fiberZero (σ := σ) (c := c) (k := k) (r := r) (x := x)] at h
  exact h

end ClaudeCyclesARZN
