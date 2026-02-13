

theorem P2_of_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (interior A))) := by
  simpa using
    (Topology.P2_of_open (A := interior (closure (interior A))) isOpen_interior)