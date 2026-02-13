

theorem Topology.P1_of_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hBsubset : B ⊆ closure (interior A)) :
    Topology.P1 B := by
  dsimp [Topology.P1] at *
  intro x hxB
  -- `x` is in `closure (interior A)` by assumption.
  have hxA : x ∈ closure (interior A) := hBsubset hxB
  -- Since `A ⊆ B`, we have `interior A ⊆ interior B`.
  have hInt : interior A ⊆ interior B := interior_mono hAB
  -- Taking closures preserves this inclusion.
  have hCl : closure (interior A) ⊆ closure (interior B) := closure_mono hInt
  -- Conclude the desired membership.
  exact hCl hxA