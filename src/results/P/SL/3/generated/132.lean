

theorem P1_empty_iff_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ↔ Topology.P3 (∅ : Set X) := by
  have h₁ : Topology.P1 (∅ : Set X) ↔ Topology.P2 (∅ : Set X) :=
    P1_empty_iff_P2_empty (X := X)
  have h₂ : Topology.P3 (∅ : Set X) ↔ Topology.P2 (∅ : Set X) :=
    P3_empty_iff_P2_empty (X := X)
  simpa using h₁.trans h₂.symm