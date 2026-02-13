

theorem Topology.closure_interior_union_eq_closure_of_isOpen {X : Type*}
    [TopologicalSpace X] {A B : Set X} (hA_open : IsOpen (A : Set X))
    (hB_open : IsOpen (B : Set X)) :
    closure (interior ((A ∪ B) : Set X)) = closure (A ∪ B) := by
  have h_open : IsOpen ((A ∪ B) : Set X) := hA_open.union hB_open
  simpa [h_open.interior_eq]