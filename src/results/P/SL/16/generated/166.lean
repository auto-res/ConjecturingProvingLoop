

theorem Topology.interior_iUnion_eq_iUnion {ι X : Type*} [TopologicalSpace X]
    {A : ι → Set X} (hOpen : ∀ i, IsOpen (A i)) :
    interior (⋃ i, A i : Set X) = ⋃ i, A i := by
  classical
  -- The union of open sets is open.
  have hUnionOpen : IsOpen (⋃ i, A i : Set X) := by
    apply isOpen_iUnion
    intro i
    exact hOpen i
  -- For an open set, its interior is itself.
  simpa [hUnionOpen.interior_eq]