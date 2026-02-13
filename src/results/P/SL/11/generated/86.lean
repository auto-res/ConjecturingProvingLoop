

theorem P1_of_interior_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior (closure A)))) := by
  simpa using
    (Topology.P1_of_open
        (A := interior (closure (interior (closure A)))) isOpen_interior)