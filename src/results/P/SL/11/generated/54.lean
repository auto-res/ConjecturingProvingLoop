

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _; exact Topology.P2_of_open (A := A) hA
  · intro _; exact Topology.P1_of_open (A := A) hA