

theorem Topology.isClosed_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → Topology.P2 A := by
  intro hClosed hP3
  have hP1 : Topology.P1 A :=
    Topology.isClosed_P3_implies_P1 (A := A) hClosed hP3
  exact (Topology.P2_iff_P1_and_P3 (A := A)).2 ⟨hP1, hP3⟩