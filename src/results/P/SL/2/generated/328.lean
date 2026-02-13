

theorem Topology.frontier_eq_self_of_isClosed_of_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → interior (A : Set X) = (∅ : Set X) →
      frontier (A : Set X) = A := by
  intro hClosed hIntEmpty
  have h :=
    Topology.frontier_eq_self_diff_interior_of_isClosed (A := A) hClosed
  simpa [hIntEmpty, Set.diff_empty] using h