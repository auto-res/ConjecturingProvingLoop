

theorem Topology.dense_left_implies_P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (A : Set X) → Topology.P3 (A ∪ B) := by
  intro hDense
  have h : Topology.P3 (B ∪ A) :=
    Topology.dense_right_implies_P3_union (A := B) (B := A) hDense
  simpa [Set.union_comm] using h