

theorem isOpen_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 (closure (A : Set X))) :
    IsOpen (closure (A : Set X)) := by
  simpa using (Topology.P3_closure_iff_open (A := A)).1 h