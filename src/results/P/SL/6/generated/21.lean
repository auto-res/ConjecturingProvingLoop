

theorem interior_closure_interior_closure_satisfies_P2
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (interior (closure A)))) := by
  simpa using
    (Topology.interior_closure_satisfies_P2 (A := interior (closure A)))