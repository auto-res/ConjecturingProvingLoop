

theorem Topology.interior_iUnion_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    interior (⋃ i, interior (F i) : Set X) = ⋃ i, interior (F i) := by
  -- The union of the interiors is open, hence its interior is itself.
  have hOpen : IsOpen (⋃ i, interior (F i) : Set X) := by
    apply isOpen_iUnion
    intro i
    exact isOpen_interior
  simpa [hOpen.interior_eq]