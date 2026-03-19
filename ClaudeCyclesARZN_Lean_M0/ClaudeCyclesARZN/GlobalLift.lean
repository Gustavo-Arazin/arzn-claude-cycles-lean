import ClaudeCyclesARZN.FiberSlices
import Mathlib

namespace ClaudeCyclesARZN

/-- Global reachability under the color-`c` successor map. -/
def ReachesBySucc {m : Nat} (σ : LocalRule m) (c : Color) (x y : VZ m) : Prop :=
  ∃ n : Nat, succPow σ c n x = y

/-- Reachability inside the reference fiber under the return map. -/
def ReachesByReturn {m : Nat} (σ : LocalRule m) (c : Color)
    (x y : FiberZero m) : Prop :=
  ∃ k : Nat, returnPowOnFiberZero σ c k x = y

/-- If `y` is reached from `x` inside `F_0` by the return map,
then every residual lift of `y` is reached globally from `x`. -/
theorem lift_return_reach_to_global_slice {m : Nat} (σ : LocalRule m) (c : Color)
    (x y : FiberZero m) (r : Nat)
    (hy : ReachesByReturn σ c x y) :
    ReachesBySucc σ c x.1 (residualMapFromFiberZero σ c r y).1 := by
  rcases hy with ⟨k, hk⟩
  refine ⟨k * m + r, ?_⟩
  have h :=
    succPow_factor_from_fiberZero (σ := σ) (c := c) (k := k) (r := r) (x := x)
  rw [hk] at h
  exact h.symm

/-- A packaged hypothesis: the return orbit from `x` covers the whole reference fiber `F_0`. -/
def ReturnOrbitCoversFiberZero {m : Nat} (σ : LocalRule m) (c : Color)
    (x : FiberZero m) : Prop :=
  ∀ y : FiberZero m, ReachesByReturn σ c x y

/-- A packaged conclusion: the global orbit from `x.1` hits every residual lift
of every point in `F_0`, across all fibers `F_r`. -/
def GlobalOrbitHitsResidualSlices {m : Nat} (σ : LocalRule m) (c : Color)
    (x : FiberZero m) : Prop :=
  ∀ (r : Nat) (y : FiberZero m),
    ReachesBySucc σ c x.1 (residualMapFromFiberZero σ c r y).1

/-- Return-orbit coverage on `F_0` lifts to global reachability of all residual slices. -/
theorem returnOrbitCoversFiberZero_lifts {m : Nat} (σ : LocalRule m) (c : Color)
    (x : FiberZero m)
    (h : ReturnOrbitCoversFiberZero σ c x) :
    GlobalOrbitHitsResidualSlices σ c x := by
  intro r y
  exact lift_return_reach_to_global_slice (σ := σ) (c := c) (x := x) (y := y) (r := r) (h y)

end ClaudeCyclesARZN
