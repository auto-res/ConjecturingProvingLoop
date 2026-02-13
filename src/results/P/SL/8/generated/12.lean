

theorem isOpen_P1_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _hP1
    exact Topology.isOpen_imp_P2 (X := X) (A := A) hA
  · intro hP2
    exact Topology.P2_imp_P1 (X := X) (A := A) hP2