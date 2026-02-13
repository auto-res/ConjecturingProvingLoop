

theorem interior_closure_inter_left_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B : Set X)) ⊆ interior (closure A) := by
  -- `closure` is monotone, hence the closure of an intersection
  -- is contained in the closure of the left factor.
  have h : closure (A ∩ B : Set X) ⊆ closure A := by
    apply closure_mono
    exact Set.inter_subset_left
  -- Taking interiors preserves inclusions.
  exact interior_mono h