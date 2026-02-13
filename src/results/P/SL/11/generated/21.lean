

theorem P2_of_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure A)) := by
  simpa using
    (Topology.P2_of_open (A := interior (closure A)) isOpen_interior)