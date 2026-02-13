

theorem Topology.P1_and_P3_iff_P2' {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P1 A ∧ Topology.P3 A) ↔ Topology.P2 A := by
  simpa using (Topology.P2_iff_P1_and_P3 (A := A)).symm