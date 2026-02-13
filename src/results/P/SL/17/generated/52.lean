

theorem Topology.P3_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (interior A))) := by
  simpa using
    (Topology.P3_of_isOpen (A := interior (closure (interior A))) isOpen_interior)