

theorem Topology.interior_iUnion_interior_eq_iUnion_interior
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    interior (⋃ i, interior (A i) : Set X) = ⋃ i, interior (A i) := by
  classical
  -- The union of the open sets `interior (A i)` is open.
  have hOpen : IsOpen (⋃ i, interior (A i) : Set X) := by
    apply isOpen_iUnion
    intro i
    exact isOpen_interior
  -- For an open set `U`, we have `interior U = U`.
  simpa [hOpen.interior_eq]