

theorem interior_closure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B : Set X)) ⊆
      interior (closure (A : Set X)) := by
  -- `A \ B` is contained in `A`.
  have hSub : (A \ B : Set X) ⊆ A := Set.diff_subset
  -- The `closure` operator preserves inclusions.
  have hClos : closure (A \ B : Set X) ⊆ closure (A : Set X) :=
    closure_mono hSub
  -- Taking interiors preserves inclusions as well.
  exact interior_mono hClos