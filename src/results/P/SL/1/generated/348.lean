

theorem Topology.isOpen_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → IsOpen (closure A) := by
  intro hDense
  have hEq : closure A = (Set.univ : Set X) := hDense.closure_eq
  simpa [hEq] using isOpen_univ