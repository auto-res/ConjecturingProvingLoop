

theorem P1_iff_P2_and_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ↔
      (Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X)) := by
  -- All three properties hold for the empty set, so the equivalence is immediate.
  have hP1 : Topology.P1 (∅ : Set X) := Topology.P1_empty (X := X)
  have hP2 : Topology.P2 (∅ : Set X) := Topology.P2_empty (X := X)
  have hP3 : Topology.P3 (∅ : Set X) := Topology.P3_empty (X := X)
  constructor
  · intro _; exact And.intro hP2 hP3
  · intro _; exact hP1