

theorem Topology.P1_P2_P3_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hOpen : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact Topology.IsOpen_P1_P2_P3 (A := A) hOpen