

theorem closed_P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  have hA_open : IsOpen A :=
    Topology.closed_P2_isOpen (X := X) (A := A) hA_closed hP2
  exact Topology.isOpen_imp_P1 (X := X) (A := A) hA_open