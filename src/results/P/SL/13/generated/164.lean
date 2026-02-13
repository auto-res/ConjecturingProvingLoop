

theorem Topology.interior_union_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hB_open : IsOpen (B : Set X)) :
    interior ((A ∪ B) : Set X) = A ∪ B := by
  have h_open : IsOpen ((A ∪ B) : Set X) := hA_open.union hB_open
  simpa [h_open.interior_eq]