

theorem Topology.closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure A) → closure (interior (closure A)) = closure A := by
  intro hP1
  simpa using
    (Topology.closure_interior_eq_of_isClosed_of_P1 (A := closure A) isClosed_closure hP1)