

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P1_and_P3 (X := X) (A := A) hP2
  · rintro ⟨hP1, hP3⟩
    exact Topology.P3_and_P1_implies_P2 (X := X) (A := A) hP3 hP1