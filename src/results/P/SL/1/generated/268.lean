

theorem Topology.P2_union_of_dense_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : Dense (interior B)) :
    Topology.P2 (A ∪ B) := by
  -- First, obtain density of `interior (A ∪ B)` by symmetry.
  have hDense : Dense (interior (A ∪ B)) := by
    have h := Topology.dense_interior_union_of_dense_left (A := B) (B := A) hB
    simpa [Set.union_comm] using h
  -- Apply the existing lemma to conclude the `P2` property.
  exact Topology.P2_of_dense_interior (A := A ∪ B) hDense