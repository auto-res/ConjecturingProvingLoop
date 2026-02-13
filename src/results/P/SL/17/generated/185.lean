

theorem Topology.P_properties_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hA_open : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  simpa using
    (Topology.P_properties_of_isOpen (A := A) hA_open)