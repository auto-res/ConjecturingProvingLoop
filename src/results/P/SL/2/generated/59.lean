

theorem Topology.P2_iff_P3_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (Topology.P2 A ↔ Topology.P3 A) := by
  intro hP1
  have hEquiv := (Topology.P2_iff_P1_and_P3 (A := A))
  constructor
  · intro hP2
    have h := (hEquiv).1 hP2
    exact h.right
  · intro hP3
    exact (hEquiv).2 ⟨hP1, hP3⟩