

theorem Topology.P2_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure A)) := by
  simpa using
    (Topology.isOpen_implies_P2 (A := interior (closure A)) isOpen_interior)