

theorem Topology.dense_implies_interior_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (A : Set X) →
      interior (closure (A : Set X)) = (Set.univ : Set X) := by
  intro hDense
  have h_cl : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  simpa [h_cl, interior_univ]