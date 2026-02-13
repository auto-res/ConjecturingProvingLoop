

theorem interior_closure_inter_right_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B : Set X)) ⊆ interior (closure B) := by
  -- `closure` is monotone, hence `closure (A ∩ B)` is contained in `closure B`.
  have h : closure (A ∩ B : Set X) ⊆ closure B := by
    apply closure_mono
    exact Set.inter_subset_right
  -- Taking interiors preserves inclusions.
  exact interior_mono h