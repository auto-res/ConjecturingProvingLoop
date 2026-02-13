

theorem P2_implies_P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (interior A) := by
  intro hP2
  have hP1 : Topology.P1 A :=
    (Topology.P2_implies_P1 (X := X) (A := A)) hP2
  exact (Topology.P1_implies_P1_interior (X := X) (A := A)) hP1