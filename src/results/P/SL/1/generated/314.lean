

theorem Topology.P3_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsOpen (closure A)) : Topology.P3 (closure A) := by
  exact (Topology.P3_closure_iff_isOpen_closure (A := A)).2 h