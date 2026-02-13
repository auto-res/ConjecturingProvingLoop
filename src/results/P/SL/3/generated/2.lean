

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hA
  exact ⟨P2_implies_P1 hA, P2_implies_P3 hA⟩