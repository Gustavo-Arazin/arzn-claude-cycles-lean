import ClaudeCyclesARZN.Torus
import Mathlib

namespace ClaudeCyclesARZN

/-- The fiber of index `s` is the set of vertices whose coordinate sum is `s`. -/
def Fiber (m : Nat) (s : ZMod m) : Set (VZ m) :=
  {v | fiberIndex v = s}

/-- The `c`-successor map sends the fiber `F_s` into the next fiber `F_{s+1}`. -/
theorem succ_maps_fiber_to_next {m : Nat} (σ : LocalRule m) (c : Color)
    {s : ZMod m} {v : VZ m} (hv : v ∈ Fiber m s) :
    succ σ c v ∈ Fiber m (s + 1) := by
  dsimp [Fiber] at hv ⊢
  rw [fiberIndex_succ, hv]

/-- Set-theoretic image formulation of the same fiber-shift lemma. -/
theorem image_Fiber_subset_next {m : Nat} (σ : LocalRule m) (c : Color) (s : ZMod m) :
    succ σ c '' Fiber m s ⊆ Fiber m (s + 1) := by
  intro w hw
  rcases hw with ⟨v, hv, rfl⟩
  exact succ_maps_fiber_to_next σ c hv

end ClaudeCyclesARZN
