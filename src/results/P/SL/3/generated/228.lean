

theorem P1_P2_P3_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  simpa using (Topology.P1_P2_P3_of_isOpen (A := A) hOpen)