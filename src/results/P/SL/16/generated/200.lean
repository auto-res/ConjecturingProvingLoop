

theorem Topology.closure_interior_closure_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hOpen : IsOpen (closure A)) :
    closure (interior (closure A)) = closure A := by
  simpa using
    (Topology.closure_interior_eq_closure_of_isOpen (X := X) (A := closure A) hOpen)