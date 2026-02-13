

theorem Topology.interior_iUnion_eq_of_isOpen {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} (hOpen : ∀ i, IsOpen (A i)) :
    interior (Set.iUnion A) = Set.iUnion A := by
  have hOpenUnion : IsOpen (Set.iUnion A) := isOpen_iUnion hOpen
  simpa using hOpenUnion.interior_eq