

theorem P1_iff_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ↔ Topology.P3 (∅ : Set X) := by
  have h₁ := (Topology.P1_iff_P2_empty (X := X))
  have h₂ := (Topology.P2_iff_P3_empty (X := X))
  exact h₁.trans h₂