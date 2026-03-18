import ClaudeCyclesARZN.Fiber
import Mathlib

namespace ClaudeCyclesARZN

/-- `succPow σ c n v` is the result of applying the color-`c` successor
`n` times to the vertex `v`. -/
def succPow {m : Nat} (σ : LocalRule m) (c : Color) : Nat → VZ m → VZ m
  | 0, v => v
  | n + 1, v => succ σ c (succPow σ c n v)

@[simp] theorem succPow_zero {m : Nat} (σ : LocalRule m) (c : Color) (v : VZ m) :
    succPow σ c 0 v = v := rfl

@[simp] theorem succPow_succ {m : Nat} (σ : LocalRule m) (c : Color) (n : Nat) (v : VZ m) :
    succPow σ c (n + 1) v = succ σ c (succPow σ c n v) := rfl

/-- After `n` successor steps, the fiber index has increased by `n` modulo `m`. -/
theorem fiberIndex_succPow {m : Nat} (σ : LocalRule m) (c : Color) (n : Nat) (v : VZ m) :
    fiberIndex (succPow σ c n v) = fiberIndex v + (n : ZMod m) := by
  induction n generalizing v with
  | zero =>
      simp [succPow]
  | succ n ih =>
      simp [succPow, fiberIndex_succ, ih, add_assoc]

/-- Iterating the successor `n` times sends `F_s` into `F_{s+n}`. -/
theorem succPow_maps_fiber {m : Nat} (σ : LocalRule m) (c : Color) (n : Nat)
    {s : ZMod m} {v : VZ m} (hv : v ∈ Fiber m s) :
    succPow σ c n v ∈ Fiber m (s + (n : ZMod m)) := by
  dsimp [Fiber] at hv ⊢
  rw [fiberIndex_succPow, hv]

/-- The `m`-step return map induced by the color-`c` successor. -/
def returnMap {m : Nat} (σ : LocalRule m) (c : Color) : VZ m → VZ m :=
  succPow σ c m

/-- The return map preserves every fiber. -/
theorem returnMap_preserves_fiber {m : Nat} (σ : LocalRule m) (c : Color)
    {s : ZMod m} {v : VZ m} (hv : v ∈ Fiber m s) :
    returnMap σ c v ∈ Fiber m s := by
  have h :=
    succPow_maps_fiber (σ := σ) (c := c) (n := m) (s := s) hv
  simpa [returnMap] using h

/-- Set-theoretic image formulation: the return map preserves each fiber. -/
theorem image_returnMap_subset_same {m : Nat} (σ : LocalRule m) (c : Color) (s : ZMod m) :
    returnMap σ c '' Fiber m s ⊆ Fiber m s := by
  intro w hw
  rcases hw with ⟨v, hv, rfl⟩
  exact returnMap_preserves_fiber (σ := σ) (c := c) hv

end ClaudeCyclesARZN
