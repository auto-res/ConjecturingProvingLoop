

theorem Topology.frontier_eq_self_of_isClosed_and_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hInt : interior A = (∅ : Set X)) :
    frontier A = A := by
  have h :=
    Topology.frontier_eq_self_diff_interior_of_isClosed
      (X := X) (A := A) hA
  simpa [hInt] using h