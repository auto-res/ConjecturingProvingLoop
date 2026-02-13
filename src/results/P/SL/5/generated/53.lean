

theorem P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A := by
  constructor
  · intro _hP1
    exact Topology.isOpen_implies_P2 (X := X) (A := A) hA
  · intro hP2
    exact Topology.P2_implies_P1 (X := X) (A := A) hP2