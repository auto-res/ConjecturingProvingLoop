

theorem Topology.dense_implies_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → IsOpen (closure (A : Set X)) := by
  intro hDense
  simpa [hDense.closure_eq] using (isOpen_univ : IsOpen (Set.univ : Set X))