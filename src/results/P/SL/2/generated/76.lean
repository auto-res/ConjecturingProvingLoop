

theorem Topology.P1_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure (A : Set X)))) := by
  simpa using
    (Topology.P1_closure_interior (A := closure (A : Set X)))