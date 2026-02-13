

theorem Topology.closed_dense_interior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (h_dense : Dense (A : Set X)) :
    interior (A : Set X) = (Set.univ : Set X) := by
  have h_eq : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (X := X) (A := A) h_closed h_dense
  simpa [h_eq, interior_univ]