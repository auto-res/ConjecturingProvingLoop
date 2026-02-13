

theorem closed_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_imp_P3 (X := X) (A := A) hP2
  · intro hP3
    have hA_open : IsOpen A :=
      Topology.closed_P3_isOpen (X := X) (A := A) hA_closed hP3
    exact Topology.isOpen_imp_P2 (X := X) (A := A) hA_open