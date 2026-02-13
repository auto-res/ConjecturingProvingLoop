

theorem Topology.interior_closure_interior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (∅ : Set X) ↔ interior (A : Set X) = ∅ := by
  constructor
  · intro h
    -- `interior A` is contained in `interior (closure (interior A))`,
    -- hence is empty if the latter is.
    have hsubset :
        interior (A : Set X) ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (X := X) (A := A)
    have hsubset' : interior (A : Set X) ⊆ (∅ : Set X) := by
      simpa [h] using hsubset
    -- Conclude the desired equality.
    apply Set.Subset.antisymm hsubset'
    intro x hx; cases hx
  · intro h
    -- Rewrite using `h` to reduce to the empty set.
    simpa [h, closure_empty, interior_empty]