

theorem Topology.isOpen_closure_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 (X := X) (closure (A : Set X))) :
    IsOpen (closure A) := by
  exact (Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)).1 h