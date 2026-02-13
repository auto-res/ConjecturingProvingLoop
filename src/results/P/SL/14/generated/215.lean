

theorem Topology.dense_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Dense (closure (A : Set X)) := by
  intro hDense
  have h_eq : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  have h_closure_eq : closure (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [closure_closure, h_eq, closure_univ]
  exact (dense_iff_closure_eq).2 h_closure_eq