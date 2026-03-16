import Mathlib

/-!
# Core (M0): Formal scaffolding for Claude's Cycles

This file is intentionally construction-agnostic.

It formalizes:
* the vertex type `V m = (Fin m)^3`;
* a notion of "colored successor maps" `f_c : V m → V m`;
* sufficient conditions for each `f_c` to define a directed Hamiltonian cycle
  (as a single orbit under iteration);
* disjointness of colored arc-sets given pointwise distinct successors.

The next milestones will implement an explicit even-case rule `σ_even`
and prove it satisfies these conditions.
-/

namespace ClaudeCyclesARZN

open Function

/-- Vertex set of the m×m×m directed torus. -/
abbrev V (m : Nat) : Type := Fin m × Fin m × Fin m

/-- A directed arc. -/
abbrev Arc (α : Type) : Type := α × α

/-- Arc-set induced by a successor function `f : α → α`: all arcs `(v, f v)`. -/
def arcSet {α : Type} (f : α → α) : Set (Arc α) :=
  {a | ∃ v, a = (v, f v)}

/-- Two successor functions are arc-disjoint if they never choose the same outgoing arc. -/
def outgoingDistinct {α : Type} (f g : α → α) : Prop :=
  ∀ v, f v ≠ g v

/-- If successors are pointwise distinct, their arc-sets are disjoint. -/
theorem arcSet_disjoint_of_outgoingDistinct {α : Type} {f g : α → α}
    (h : outgoingDistinct f g) :
    Disjoint (arcSet f) (arcSet g) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro a ha hb
  rcases ha with ⟨v, rfl⟩
  rcases hb with ⟨w, hw⟩
  -- (v, f v) = (w, g w) implies v = w and f v = g v
  have : v = w := by
    -- compare first components
    simpa [Prod.ext_iff] using congrArg Prod.fst hw
  subst this
  have : f w = g w := by
    simpa [Prod.ext_iff] using congrArg Prod.snd hw
  exact (h w) this

/-- A successor function is "permutation-like" if it is bijective. -/
def IsPermutation {α : Type} (f : α → α) : Prop := Function.Bijective f

/-- A successor function has a single orbit if some start vertex reaches every vertex by iteration. -/
def IsSingleOrbit {α : Type} (f : α → α) : Prop :=
  ∃ v0 : α, ∀ v : α, ∃ n : Nat, (f^[n]) v0 = v

/-- Our working definition of "directed Hamiltonian cycle" for a successor map. -/
def IsHamiltonian {α : Type} (f : α → α) : Prop :=
  IsPermutation f ∧ IsSingleOrbit f

/-- "Indegree = 1" in the functional digraph of `f` follows from injectivity. -/
theorem unique_preimage_of_injective {α : Type} {f : α → α}
    (hinj : Function.Injective f) :
    ∀ v : α, ∀ x y : α, f x = v → f y = v → x = y := by
  intro v x y hx hy
  exact hinj (hx.trans hy.symm)

/-- A basic corollary: if `f` is bijective then every vertex has exactly one predecessor. -/
theorem indegree_one_of_IsPermutation {α : Type} {f : α → α}
    (hperm : IsPermutation f) :
    ∀ v : α, ∃! u : α, f u = v := by
  classical
  intro v
  rcases hperm.2 v with ⟨u, hu⟩
  refine ⟨u, hu, ?_⟩
  intro y hy
  exact (unique_preimage_of_injective (hperm.1) v y u hy hu)

/-!
## 3-color framework

We represent a 3-color decomposition by three successor maps `f0 f1 f2 : V m → V m`.

Later milestones will derive these successor maps from a local rule
`σ : V m → Equiv (Fin 3) Axis` and the three "bump" edges of the torus.

For M0 we keep it abstract to focus on proof infrastructure.
-/

/-- A 3-color successor family. -/
structure ThreeSucc (α : Type) where
  f0 : α → α
  f1 : α → α
  f2 : α → α

namespace ThreeSucc

variable {α : Type}

def arcSet0 (S : ThreeSucc α) : Set (Arc α) := arcSet S.f0
def arcSet1 (S : ThreeSucc α) : Set (Arc α) := arcSet S.f1
def arcSet2 (S : ThreeSucc α) : Set (Arc α) := arcSet S.f2

/-- Pairwise arc-disjointness implied by pointwise distinctness. -/
theorem pairwise_disjoint_of_outgoingDistinct (S : ThreeSucc α)
    (h01 : outgoingDistinct S.f0 S.f1)
    (h02 : outgoingDistinct S.f0 S.f2)
    (h12 : outgoingDistinct S.f1 S.f2) :
    Disjoint S.arcSet0 S.arcSet1 ∧ Disjoint S.arcSet0 S.arcSet2 ∧ Disjoint S.arcSet1 S.arcSet2 := by
  refine ⟨arcSet_disjoint_of_outgoingDistinct h01, ?_, arcSet_disjoint_of_outgoingDistinct h12⟩
  exact arcSet_disjoint_of_outgoingDistinct h02

/-- M0 "valid decomposition" predicate: each color is Hamiltonian (definition-level), and arc-sets are disjoint. -/
def IsValid (S : ThreeSucc α) : Prop :=
  IsHamiltonian S.f0 ∧ IsHamiltonian S.f1 ∧ IsHamiltonian S.f2 ∧
  outgoingDistinct S.f0 S.f1 ∧ outgoingDistinct S.f0 S.f2 ∧ outgoingDistinct S.f1 S.f2

end ThreeSucc

end ClaudeCyclesARZN
