

theorem P3_of_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior (closure A)))) := by
  simpa using
    (Topology.P3_of_open
        (A := interior (closure (interior (closure A)))) isOpen_interior)