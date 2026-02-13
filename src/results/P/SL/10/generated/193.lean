

theorem Topology.interior_iUnion_interior_eq {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    interior (⋃ i, interior (A i)) = ⋃ i, interior (A i) := by
  have h_open : IsOpen (⋃ i, interior (A i)) := by
    refine isOpen_iUnion (fun _ => isOpen_interior)
  simpa using h_open.interior_eq