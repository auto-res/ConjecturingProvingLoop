

theorem dense_union_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseB : Dense (B : Set X)) :
    Dense (A ∪ B : Set X) := by
  simpa [Set.union_comm] using
    (Topology.dense_union_left (A := B) (B := A) hDenseB)