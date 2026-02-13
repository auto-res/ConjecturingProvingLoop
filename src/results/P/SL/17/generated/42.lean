

theorem Topology.P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure A)) := by
  simpa using
    (Topology.P3_of_isOpen (A := interior (closure A)) isOpen_interior)