

theorem dense_iff_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ interior (closure (A : Set X)) = Set.univ := by
  constructor
  · intro hDense
    exact Topology.interior_closure_eq_univ_of_dense (A := A) hDense
  · intro hInt
    exact Topology.dense_of_interior_closure_eq_univ (A := A) hInt