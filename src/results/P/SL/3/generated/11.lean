

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _; exact Topology.P2_of_isOpen (A := A) hA
  · intro h; exact Topology.P2_implies_P1 (A := A) h