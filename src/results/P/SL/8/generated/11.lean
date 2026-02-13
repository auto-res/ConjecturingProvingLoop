

theorem closed_P2_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    IsOpen A := by
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  exact Topology.closed_P3_isOpen (X := X) (A := A) hA_closed hP3