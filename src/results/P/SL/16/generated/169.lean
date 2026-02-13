

theorem Topology.interior_union_eq_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B : Set X) = A ∪ B := by
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  simpa using hOpen.interior_eq