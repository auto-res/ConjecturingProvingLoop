

theorem interior_closure_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B : Set X)) ⊆ interior (closure A) := by
  -- Since `A \ B ⊆ A`, their closures satisfy the same inclusion.
  have hsubset : closure (A \ B : Set X) ⊆ closure A :=
    closure_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)
  -- Monotonicity of `interior` yields the desired result.
  exact interior_mono hsubset