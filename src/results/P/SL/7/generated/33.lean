

theorem Topology.IsOpen_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP2 : Topology.P2 A := (Topology.IsOpen_P2 (A := A) hA)
  have hP1P3 : Topology.P1 A ∧ Topology.P3 A := (Topology.IsOpen_P1_and_P3 (A := A) hA)
  exact ⟨hP1P3.1, hP2, hP1P3.2⟩