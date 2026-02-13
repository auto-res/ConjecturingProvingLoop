

theorem Topology.isOpen_iff_subset_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A ↔ A ⊆ interior A := by
  constructor
  · intro hOpen
    -- For an open set, its interior is itself.
    have h_eq : interior A = A := hOpen.interior_eq
    -- Rewriting with this equality yields the inclusion.
    simpa [h_eq]
  · intro hSubset
    -- `interior A` is open, and the assumed inclusion together with `interior_subset`
    -- gives equality of the two sets.
    have h_eq : interior A = A := by
      apply subset_antisymm
      · exact interior_subset
      · exact hSubset
    -- Conclude that `A` is open by rewriting.
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))