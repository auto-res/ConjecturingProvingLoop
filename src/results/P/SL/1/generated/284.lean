

theorem Topology.dense_union_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense B → Dense (A ∪ B) := by
  intro hB
  simpa [Set.union_comm] using
    (Topology.dense_union_left (A := B) (B := A) hB)