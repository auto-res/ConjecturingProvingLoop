

theorem Topology.interior_closure_interior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in `interior (closure (interior A))`.
    have hsubset : interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (A := A)
    -- Hence `interior A` must be empty.
    have hSubEmpty : interior A ⊆ (∅ : Set X) := by
      intro x hx
      have : x ∈ interior (closure (interior A)) := hsubset hx
      simpa [h] using this
    exact Set.Subset.antisymm hSubEmpty (Set.empty_subset _)
  · intro h
    -- Rewrite and simplify using `h`.
    simpa [h, closure_empty, interior_empty]