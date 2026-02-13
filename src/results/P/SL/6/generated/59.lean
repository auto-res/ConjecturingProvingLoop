

theorem interior_closure_interior_satisfies_P2
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (interior A))) := by
  simpa using
    (Topology.interior_closure_satisfies_P2 (A := interior A))