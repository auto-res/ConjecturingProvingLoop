

@[simp] theorem Topology.closure_interior_closure_interior_simp
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  simpa using
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A)