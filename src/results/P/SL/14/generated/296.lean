

theorem Topology.dense_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (B : Set X) → Dense (A ∪ B : Set X) := by
  intro hDenseB
  have h : Dense (B ∪ A : Set X) := by
    simpa using
      Topology.dense_union_left (X := X) (A := B) (B := A) hDenseB
  simpa [Set.union_comm] using h