

theorem interior_has_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ∧ Topology.P3 (interior A) := by
  have hP2 : Topology.P2 (interior A) := by
    simpa using (interior_has_P2 (X := X) (A := A))
  have hP1 : Topology.P1 (interior A) := (P2_implies_P1 (X := X) (A := interior A)) hP2
  have hP3 : Topology.P3 (interior A) := (P2_implies_P3 (X := X) (A := interior A)) hP2
  exact And.intro hP1 hP3