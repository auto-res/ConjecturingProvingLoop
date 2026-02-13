

theorem P2_iterate_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (A := interior (closure (interior (closure (interior A))))) := by
  apply P2_of_open
  simpa using
    (isOpen_interior :
      IsOpen (interior (closure (interior (closure (interior A))))))