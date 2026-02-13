

theorem dense_union_has_P3_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense B → Topology.P3 (A ∪ B) := by
  intro hDenseB
  simpa [Set.union_comm] using
    (dense_union_has_P3 (X := X) (A := B) (B := A) hDenseB)