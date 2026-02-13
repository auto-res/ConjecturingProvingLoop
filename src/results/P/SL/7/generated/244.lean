

theorem Topology.subset_interior_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : A ⊆ interior A := by
  simpa [hA.interior_eq]