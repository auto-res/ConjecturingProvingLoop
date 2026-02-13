

theorem Topology.P2_of_isClosed_and_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hDense : Dense A) :
    Topology.P2 A := by
  have hEq : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (A := A) hClosed hDense
  simpa [hEq] using (P2_univ (X := X))