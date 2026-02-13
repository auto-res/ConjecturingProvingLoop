

theorem P1_iff_P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ↔ Topology.P2 (∅ : Set X) := by
  -- Both properties hold for the empty set, yielding the equivalence.
  have hP1 : Topology.P1 (∅ : Set X) := Topology.P1_empty (X := X)
  have hP2 : Topology.P2 (∅ : Set X) := Topology.P2_empty (X := X)
  exact ⟨fun _ => hP2, fun _ => hP1⟩