

theorem Topology.dense_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
  intro hDense
  simpa [hDense.closure_eq, interior_univ, closure_univ]