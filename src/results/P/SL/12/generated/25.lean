

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A := by
  constructor
  · intro _
    simpa using Topology.isOpen_P2 (X := X) (A := A) hA
  · intro _
    simpa using Topology.isOpen_P1 (X := X) (A := A) hA