

theorem Topology.frontier_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → frontier (closure (A : Set X)) = (∅ : Set X) := by
  intro hDense
  simpa [hDense.closure_eq, frontier_univ]