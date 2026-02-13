

theorem dense_closed_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    (A : Set X) = Set.univ := by
  have hClosure : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).1 hDense
  simpa [hClosed.closure_eq] using hClosure