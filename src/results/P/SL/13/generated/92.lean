

theorem Topology.closed_dense_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hA_dense : Dense (A : Set X)) :
    IsOpen (A : Set X) := by
  have h_eq : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (X := X) (A := A) hA_closed hA_dense
  simpa [h_eq] using isOpen_univ