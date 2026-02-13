

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (A := A) ↔ Topology.P2 (A := A) := by
  constructor
  · intro _; exact Topology.P2_of_isOpen (A := A) hA
  · intro _; exact Topology.P1_of_isOpen (A := A) hA