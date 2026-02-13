

theorem Topology.isOpen_dense_closure_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen A → Dense A → closure (interior A) = (Set.univ : Set X) := by
  intro hOpen hDense
  have hEq : closure (interior A) = closure A :=
    Topology.isOpen_closure_interior_eq_closure (A := A) hOpen
  simpa [hDense.closure_eq] using hEq