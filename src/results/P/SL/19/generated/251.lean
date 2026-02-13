

theorem Topology.frontier_univ_eq_empty {X : Type*} [TopologicalSpace X] :
    frontier (Set.univ : Set X) = (∅ : Set X) := by
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  have hClosed : IsClosed (Set.univ : Set X) := isClosed_univ
  simpa using
    (Topology.frontier_eq_empty_of_isOpen_and_isClosed
      (A := (Set.univ : Set X)) hOpen hClosed)