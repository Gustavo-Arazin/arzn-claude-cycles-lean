import ClaudeCyclesARZN.GlobalLift
import Mathlib

namespace ClaudeCyclesARZN

/-- Every vertex admits a residual normal form from the reference fiber `F_0`. -/
def HasResidualNormalForm {m : Nat} (σ : LocalRule m) (c : Color) : Prop :=
  ∀ z : VZ m, ∃ r : Nat, ∃ y : FiberZero m,
    (residualMapFromFiberZero σ c r y).1 = z

/-- The global orbit from `x.1` reaches every vertex of `V_m`. -/
def GlobalOrbitCoversAllVertices {m : Nat} (σ : LocalRule m) (c : Color)
    (x : FiberZero m) : Prop :=
  ∀ z : VZ m, ReachesBySucc σ c x.1 z

/-- Pointwise version of the strong reduction: a residual normal form for `z`
turns return reachability on `F_0` into global reachability of `z`. -/
theorem strongReduction_pointwise {m : Nat} (σ : LocalRule m) (c : Color)
    (x : FiberZero m) {z : VZ m}
    (hret : ReturnOrbitCoversFiberZero σ c x)
    (hz : ∃ r : Nat, ∃ y : FiberZero m,
      (residualMapFromFiberZero σ c r y).1 = z) :
    ReachesBySucc σ c x.1 z := by
  rcases hz with ⟨r, y, hy⟩
  rw [← hy]
  exact returnOrbitCoversFiberZero_lifts (σ := σ) (c := c) (x := x) hret r y

/-- Strong reduction in packaged form: if the return orbit from `x` covers `F_0`
and every vertex admits a residual normal form, then the global orbit from `x.1`
reaches every vertex of `V_m`. -/
theorem strongReduction_globalReachability {m : Nat} (σ : LocalRule m) (c : Color)
    (x : FiberZero m)
    (hret : ReturnOrbitCoversFiberZero σ c x)
    (hnf : HasResidualNormalForm σ c) :
    GlobalOrbitCoversAllVertices σ c x := by
  intro z
  exact strongReduction_pointwise (σ := σ) (c := c) (x := x) hret (hnf z)

end ClaudeCyclesARZN
