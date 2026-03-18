import ClaudeCyclesARZN.Orbit
import Mathlib

namespace ClaudeCyclesARZN

/-- Iterate the return map `k` times. -/
def returnPow {m : Nat} (σ : LocalRule m) (c : Color) : Nat → VZ m → VZ m
  | 0, v => v
  | k + 1, v => returnMap σ c (returnPow σ c k v)

@[simp] theorem returnPow_zero {m : Nat} (σ : LocalRule m) (c : Color) (v : VZ m) :
    returnPow σ c 0 v = v := rfl

@[simp] theorem returnPow_succ {m : Nat} (σ : LocalRule m) (c : Color) (k : Nat) (v : VZ m) :
    returnPow σ c (k + 1) v = returnMap σ c (returnPow σ c k v) := rfl

/-- `k` iterates of the return map equal `k*m` iterates of the successor map. -/
theorem returnPow_eq_succPow_mul {m : Nat} (σ : LocalRule m) (c : Color) (k : Nat) (v : VZ m) :
    returnPow σ c k v = succPow σ c (k * m) v := by
  induction k generalizing v with
  | zero =>
      simp [returnPow, succPow]
  | succ k ih =>
      calc
        returnPow σ c (k + 1) v
            = returnMap σ c (returnPow σ c k v) := by
                simp [returnPow]
        _ = succPow σ c m (succPow σ c (k * m) v) := by
              simp [returnMap, ih]
        _ = succPow σ c (k * m + m) v := by
              symm
              exact succPow_mul_add (σ := σ) (c := c) (k := k) (r := m) v
        _ = succPow σ c ((k + 1) * m) v := by
              rw [Nat.succ_mul]

/-- Block decomposition: `k*m + r` successor steps are `k` return steps plus `r` residual steps. -/
theorem succPow_block_decomposition {m : Nat} (σ : LocalRule m) (c : Color)
    (k r : Nat) (v : VZ m) :
    succPow σ c (k * m + r) v = succPow σ c r (returnPow σ c k v) := by
  rw [returnPow_eq_succPow_mul]
  exact succPow_mul_add (σ := σ) (c := c) (k := k) (r := r) v

/-- The return-map iterate preserves every fiber. -/
theorem returnPow_preserves_fiber {m : Nat} (σ : LocalRule m) (c : Color) (k : Nat)
    {s : ZMod m} {v : VZ m} (hv : v ∈ Fiber m s) :
    returnPow σ c k v ∈ Fiber m s := by
  rw [returnPow_eq_succPow_mul]
  exact succPow_mul_m_preserves_fiber (σ := σ) (c := c) (k := k) hv

/-- Restricted iterate of the return map on the reference fiber `F_0`. -/
def returnPowOnFiberZero {m : Nat} (σ : LocalRule m) (c : Color) :
    Nat → FiberZero m → FiberZero m
  | 0, x => x
  | k + 1, x => returnMapOnFiberZero σ c (returnPowOnFiberZero σ c k x)

@[simp] theorem returnPowOnFiberZero_zero {m : Nat} (σ : LocalRule m) (c : Color)
    (x : FiberZero m) :
    returnPowOnFiberZero σ c 0 x = x := rfl

@[simp] theorem returnPowOnFiberZero_succ {m : Nat} (σ : LocalRule m) (c : Color)
    (k : Nat) (x : FiberZero m) :
    returnPowOnFiberZero σ c (k + 1) x =
      returnMapOnFiberZero σ c (returnPowOnFiberZero σ c k x) := rfl

/-- Coercion to vertices agrees with `returnPow` on `F_0`. -/
theorem returnPowOnFiberZero_val {m : Nat} (σ : LocalRule m) (c : Color)
    (k : Nat) (x : FiberZero m) :
    (returnPowOnFiberZero σ c k x).1 = returnPow σ c k x.1 := by
  induction k generalizing x with
  | zero =>
      rfl
  | succ k ih =>
      cases x with
      | mk v hv =>
          simp [returnPowOnFiberZero, returnMapOnFiberZero, returnPow, ih]

end ClaudeCyclesARZN
