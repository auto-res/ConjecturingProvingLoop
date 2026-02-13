

theorem Topology.interior_iUnion_of_open {X : Type*} [TopologicalSpace X]
    {ι : Sort _} {F : ι → Set X} (hF : ∀ i, IsOpen (F i)) :
    interior (⋃ i, F i) = ⋃ i, F i := by
  have hOpen : IsOpen (⋃ i, F i) := isOpen_iUnion hF
  simpa using hOpen.interior_eq