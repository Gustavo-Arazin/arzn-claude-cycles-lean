import ClaudeCyclesARZN.Core
import Mathlib

namespace ClaudeCyclesARZN

/-- The vertex set of the directed 3-torus, modeled over `ZMod m`. -/
abbrev VZ (m : Nat) : Type := ZMod m × ZMod m × ZMod m

/-- Three coordinate directions. -/
inductive Axis where
  | x
  | y
  | z
  deriving DecidableEq, Repr

/-- Color labels for the three factor maps. -/
abbrev Color : Type := Fin 3

/-- Increment the first coordinate. -/
def bumpX {m : Nat} : VZ m → VZ m
  | (i, j, k) => (i + 1, j, k)

/-- Increment the second coordinate. -/
def bumpY {m : Nat} : VZ m → VZ m
  | (i, j, k) => (i, j + 1, k)

/-- Increment the third coordinate. -/
def bumpZ {m : Nat} : VZ m → VZ m
  | (i, j, k) => (i, j, k + 1)

/-- Increment the coordinate specified by the axis. -/
def bump {m : Nat} : Axis → VZ m → VZ m
  | Axis.x => bumpX
  | Axis.y => bumpY
  | Axis.z => bumpZ

/-- Sum of coordinates modulo `m`. This indexes the fibers `F_s`. -/
def fiberIndex {m : Nat} : VZ m → ZMod m
  | (i, j, k) => i + j + k

/-- A local rule assigns an axis to each color at each vertex. -/
abbrev LocalRule (m : Nat) : Type := VZ m → Color → Axis

/-- Successor map induced by a local rule for color `c`. -/
def succ {m : Nat} (σ : LocalRule m) (c : Color) : VZ m → VZ m :=
  fun v => bump (σ v c) v

theorem fiberIndex_bumpX {m : Nat} (v : VZ m) :
    fiberIndex (bumpX v) = fiberIndex v + 1 := by
  rcases v with ⟨i, j, k⟩
  change i + 1 + j + k = i + j + k + 1
  ring

theorem fiberIndex_bumpY {m : Nat} (v : VZ m) :
    fiberIndex (bumpY v) = fiberIndex v + 1 := by
  rcases v with ⟨i, j, k⟩
  change i + (j + 1) + k = i + j + k + 1
  ring

theorem fiberIndex_bumpZ {m : Nat} (v : VZ m) :
    fiberIndex (bumpZ v) = fiberIndex v + 1 := by
  rcases v with ⟨i, j, k⟩
  change i + j + (k + 1) = i + j + k + 1
  ring

/-- Every successor map advances the fiber index by one. -/
theorem fiberIndex_succ {m : Nat} (σ : LocalRule m) (c : Color) (v : VZ m) :
    fiberIndex (succ σ c v) = fiberIndex v + 1 := by
  unfold succ bump
  cases h : σ v c <;> simp [h, fiberIndex_bumpX, fiberIndex_bumpY, fiberIndex_bumpZ]

end ClaudeCyclesARZN
