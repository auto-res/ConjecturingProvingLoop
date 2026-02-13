

theorem Topology.P1_superset_of_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hBsubset : B ⊆ closure (interior A)) :
    Topology.P1 B := by
  dsimp [Topology.P1] at *
  intro x hxB
  -- `x` belongs to `closure (interior A)` by the hypothesis `hBsubset`.
  have hx_clA : x ∈ closure (interior A) := hBsubset hxB
  -- Since `A ⊆ B`, we have `interior A ⊆ interior B`.
  have hIntSubset : interior A ⊆ interior B := interior_mono hAB
  -- Taking closures preserves inclusion.
  have hClSubset : closure (interior A) ⊆ closure (interior B) :=
    closure_mono hIntSubset
  -- Conclude that `x ∈ closure (interior B)`.
  exact hClSubset hx_clA