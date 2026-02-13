

theorem P2_union₃ {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (A ∪ B ∪ C) := by
  -- First, unite `A` and `B`
  have hAB : Topology.P2 (A ∪ B) := Topology.P2_union hA hB
  -- Then unite the result with `C`
  have hABC : Topology.P2 ((A ∪ B) ∪ C) := Topology.P2_union hAB hC
  -- Rewrite the union to match the goal
  simpa [Set.union_assoc] using hABC