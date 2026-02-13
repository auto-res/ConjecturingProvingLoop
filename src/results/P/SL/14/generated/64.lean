

theorem Topology.P2_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) : Topology.P2 (closure A) := by
  exact ((Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)).2) h_open