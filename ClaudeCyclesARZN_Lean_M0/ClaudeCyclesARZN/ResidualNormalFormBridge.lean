import ClaudeCyclesARZN.StrongReduction

namespace ClaudeCyclesARZN

/--
Packaged coverage statement for the residual slices issued from the reference fiber `F₀`.

This is definitionally the same data required by `HasResidualNormalForm`; the point of
this wrapper is to expose the M3/M2e interface with a name that matches the residual-slice
language used in the paper and in the checkpoint notes.
-/
def ResidualSlicesCoverAllVertices {m : Nat} (σ : LocalRule m) (c : Color) : Prop :=
  ∀ z : VZ m, ∃ r : Nat, ∃ y : FiberZero m,
    (residualMapFromFiberZero σ c r y).1 = z

theorem residualSlicesCoverAllVertices_iff_hasResidualNormalForm
    {m : Nat} (σ : LocalRule m) (c : Color) :
    ResidualSlicesCoverAllVertices σ c ↔ HasResidualNormalForm σ c := by
  rfl

theorem hasResidualNormalForm_of_residualSlicesCoverAllVertices
    {m : Nat} {σ : LocalRule m} {c : Color}
    (hcover : ResidualSlicesCoverAllVertices σ c) :
    HasResidualNormalForm σ c := by
  exact hcover

theorem residualSlicesCoverAllVertices_of_hasResidualNormalForm
    {m : Nat} {σ : LocalRule m} {c : Color}
    (hnf : HasResidualNormalForm σ c) :
    ResidualSlicesCoverAllVertices σ c := by
  exact hnf

/--
Pointwise bridge: once a target vertex `z` is exhibited as a residual lift from `F₀`,
the strong reduction converts return-orbit coverage on `F₀` into global reachability of `z`.
-/
theorem strongReduction_pointwise_of_residualSliceWitness
    {m : Nat} (σ : LocalRule m) (c : Color)
    (x : FiberZero m) {z : VZ m}
    (hret : ReturnOrbitCoversFiberZero σ c x)
    (r : Nat) (y : FiberZero m)
    (hz : (residualMapFromFiberZero σ c r y).1 = z) :
    ReachesBySucc σ c x.1 z := by
  exact strongReduction_pointwise
    (σ := σ) (c := c) (x := x) hret ⟨r, y, hz⟩

/--
Packaged bridge: return-orbit coverage on `F₀` plus residual-slice coverage of all vertices
implies global reachability of all vertices.
-/
theorem strongReduction_of_residualSlicesCoverAllVertices
    {m : Nat} (σ : LocalRule m) (c : Color)
    (x : FiberZero m)
    (hret : ReturnOrbitCoversFiberZero σ c x)
    (hcover : ResidualSlicesCoverAllVertices σ c) :
    GlobalOrbitCoversAllVertices σ c x := by
  exact strongReduction_globalReachability
    (σ := σ) (c := c) (x := x) hret
    (hasResidualNormalForm_of_residualSlicesCoverAllVertices hcover)

end ClaudeCyclesARZN
