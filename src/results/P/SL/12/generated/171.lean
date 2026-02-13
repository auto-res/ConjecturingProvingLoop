

theorem Topology.interior_union_eq_self_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = A ∪ B := by
  have h_open : IsOpen (A ∪ B : Set X) := hA.union hB
  simpa [h_open.interior_eq]