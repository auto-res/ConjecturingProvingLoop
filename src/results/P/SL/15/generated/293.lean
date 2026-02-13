

theorem dense_right_implies_dense_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Dense B → Dense (A ∪ B) := by
  intro hDenseB
  -- Apply the corresponding lemma with the roles of `A` and `B` swapped,
  -- then rewrite using the commutativity of the union.
  have h : Dense (B ∪ A) :=
    dense_left_implies_dense_union (X := X) (A := B) (B := A) hDenseB
  simpa [Set.union_comm] using h