

theorem Topology.P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact And.intro (P2_implies_P1 (A := A) hP2) (P2_implies_P3 (A := A) hP2)
  · rintro ⟨hP1, hP3⟩
    exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3