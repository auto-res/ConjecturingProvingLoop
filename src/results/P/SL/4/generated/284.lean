

theorem frontier_diff_subset_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A \ B) ⊆ frontier A ∪ frontier B := by
  -- First rewrite the difference as an intersection and apply the existing lemma
  have h :
      frontier (A \ B) ⊆ frontier A ∪ frontier (Bᶜ) := by
    simpa [Set.diff_eq] using
      (frontier_inter_subset (A := A) (B := Bᶜ))
  -- Replace `frontier (Bᶜ)` with `frontier B`
  simpa [frontier_compl_eq_frontier (A := B)] using h