

theorem Topology.interior_union_eq_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B : Set X) = A ∪ B := by
  have hOpen : IsOpen (A ∪ B : Set X) := IsOpen.union hA hB
  simpa using hOpen.interior_eq