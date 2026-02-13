

theorem isOpen_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (closure (A : Set X))) :
    IsOpen (closure (A : Set X)) := by
  simpa using ((Topology.P2_closure_iff_open (A := A)).1 h)