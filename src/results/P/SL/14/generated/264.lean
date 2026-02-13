

theorem Topology.interior_iUnion_eq_iUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) :
    interior (⋃ i, A i : Set X) = ⋃ i, A i := by
  have hOpen : IsOpen (⋃ i, A i : Set X) := isOpen_iUnion hA
  simpa using hOpen.interior_eq