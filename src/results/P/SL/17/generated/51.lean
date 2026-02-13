

theorem Topology.P1_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) := by
  simpa using
    (Topology.P1_of_isOpen (A := interior (closure A)) isOpen_interior)