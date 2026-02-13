

theorem P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A := by
  constructor
  · intro _hP1
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hA
  · intro _hP3
    exact Topology.isOpen_implies_P1 (X := X) (A := A) hA