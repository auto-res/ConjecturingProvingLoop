

theorem Topology.isOpen_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → IsOpen (closure (A : Set X)) := by
  intro hDense
  have h_eq : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  simpa [h_eq] using (isOpen_univ : IsOpen (Set.univ : Set X))