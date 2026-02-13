

theorem P3_union_of_dense_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseB : Dense (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  simpa [Set.union_comm] using
    (Topology.P3_union_of_dense_left (A := B) (B := A) hDenseB)