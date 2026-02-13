

theorem Topology.closure_subset_closure_union_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (B : Set X) ⊆ closure (A ∪ B) := by
  -- Apply the “left‐hand” version after swapping `A` and `B`,
  -- then rewrite using commutativity of `∪`.
  have h :
      closure (B : Set X) ⊆ closure (B ∪ A) :=
    Topology.closure_subset_closure_union_left (X := X) (A := B) (B := A)
  simpa [Set.union_comm] using h