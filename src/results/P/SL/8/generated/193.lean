

theorem closed_P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  exact
    (Topology.closed_P2_iff_P3 (X := X) (A := A) hA_closed).1 hP2