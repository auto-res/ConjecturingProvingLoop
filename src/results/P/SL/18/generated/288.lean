

theorem interior_eq_univ_of_closed_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hDense : Dense (A : Set X)) :
    interior (A : Set X) = Set.univ := by
  have hA : (A : Set X) = Set.univ :=
    Topology.dense_closed_eq_univ (A := A) hDense hClosed
  simpa [hA, interior_univ]