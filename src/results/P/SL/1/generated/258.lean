

theorem Topology.P2_union_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (interior A) → Topology.P2 (A ∪ B) := by
  intro hDense
  -- First, obtain density of `interior (A ∪ B)` from the given hypothesis.
  have hDenseUnion : Dense (interior (A ∪ B)) :=
    Topology.dense_interior_union_of_dense_left (A := A) (B := B) hDense
  -- Apply the existing lemma to conclude the `P2` property.
  exact Topology.P2_of_dense_interior (A := A ∪ B) hDenseUnion