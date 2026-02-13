

theorem Topology.P1_of_between
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) (hBsubset : B ⊆ closure (interior A)) :
    Topology.P1 B := by
  dsimp [Topology.P1] at *
  intro x hxB
  -- From the assumption `B ⊆ closure (interior A)` we get
  -- that `x` lies in `closure (interior A)`.
  have hx_closureA : x ∈ closure (interior A) := hBsubset hxB
  -- Since `A ⊆ B`, we have `interior A ⊆ interior B`.
  have hInt : interior A ⊆ interior B := interior_mono hAB
  -- Taking closures preserves inclusion.
  have hCl : closure (interior A) ⊆ closure (interior B) :=
    closure_mono hInt
  -- Conclude that `x` lies in `closure (interior B)`.
  exact hCl hx_closureA