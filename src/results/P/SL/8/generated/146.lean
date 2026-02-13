

theorem closed_P3_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    Topology.P2 A := by
  have h_eq : Topology.P2 A ↔ Topology.P3 A :=
    Topology.closed_P2_iff_P3 (X := X) (A := A) hA_closed
  exact (h_eq.mpr hP3)