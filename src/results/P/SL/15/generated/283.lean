

theorem isOpen_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → IsOpen (closure A) := by
  intro hDense
  have h_eq : closure (A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [h_eq] using isOpen_univ