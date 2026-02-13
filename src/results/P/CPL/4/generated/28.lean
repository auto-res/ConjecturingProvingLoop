

theorem P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) : Topology.P1 (A ∪ B ∪ C) := by
  have hBC : Topology.P1 (B ∪ C) := P1_union (X := X) hB hC
  have hABC : Topology.P1 (A ∪ (B ∪ C)) := P1_union (X := X) hA hBC
  simpa [Set.union_assoc] using hABC