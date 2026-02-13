

theorem P2_implies_P1_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ↔ Topology.P3 A) := by
  intro hP2
  have hP1 : Topology.P1 A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  exact ⟨fun _ => hP3, fun _ => hP1⟩