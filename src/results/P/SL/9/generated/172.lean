

theorem Topology.interior_union_eq_union_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B) = A ∪ B := by
  have h_open : IsOpen (A ∪ B) := IsOpen.union hA hB
  simpa using h_open.interior_eq