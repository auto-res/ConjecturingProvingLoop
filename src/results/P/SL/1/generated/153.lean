

theorem Topology.P2_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) : Topology.P2 (closure A) := by
  exact Topology.P2_of_isOpen (A := closure A) hOpen