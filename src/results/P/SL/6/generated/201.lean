

theorem interior_closure_interior_closure_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior (closure (A : Set X))))) := by
  simpa using
    (Topology.interior_closure_interior_satisfies_P1
      (A := closure (A : Set X)))