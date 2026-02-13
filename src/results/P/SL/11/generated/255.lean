

theorem interior_closure_diff_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  -- Step 1:  `A \ B` is contained in `A ∪ B`.
  have hSub : (A \ B : Set X) ⊆ A ∪ B := by
    intro y hy
    exact Or.inl hy.1
  -- Step 2:  Taking closures preserves the inclusion.
  have hClSub : closure (A \ B) ⊆ closure (A ∪ B) :=
    closure_mono hSub
  -- Step 3:  Monotonicity of `interior` yields the desired result.
  exact (interior_mono hClSub) hx