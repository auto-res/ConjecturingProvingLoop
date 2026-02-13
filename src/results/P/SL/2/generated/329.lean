

theorem Topology.dense_implies_frontier_interior_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → frontier (interior (closure (A : Set X))) = (∅ : Set X) := by
  intro hDense
  have hInt : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simp [hDense.closure_eq, interior_univ]
  simpa [hInt, frontier_univ]