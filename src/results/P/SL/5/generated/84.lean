

theorem P1_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (closure (interior (closure A))) := by
  simpa using
    (Topology.P1_closure_interior (X := X) (A := closure A))