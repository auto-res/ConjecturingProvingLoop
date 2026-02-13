

theorem P2_union_implies_P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P1 (A ∪ B) := by
  intro hP2A hP2B
  -- From `P2` we derive `P1` for each set.
  have hP1A : Topology.P1 A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2A
  have hP1B : Topology.P1 B :=
    Topology.P2_implies_P1 (X := X) (A := B) hP2B
  -- The union of two `P1` sets again satisfies `P1`.
  exact
    Topology.P1_union (X := X) (A := A) (B := B) hP1A hP1B