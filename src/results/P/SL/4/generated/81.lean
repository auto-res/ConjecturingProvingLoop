

theorem P2_closed_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  -- From closedness, `P2` is equivalent to `P3`.
  have hP3 : Topology.P3 A :=
    ((Topology.P2_iff_P3_of_closed (A := A) hA).1) hP2
  -- A closed set satisfying `P3` also satisfies `P1`.
  exact (Topology.P3_closed_imp_P1 (A := A) hA) hP3