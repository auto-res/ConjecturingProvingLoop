

theorem interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ interior (closure A) := by
  -- The inclusion `A ⊆ closure A` is basic.
  have hSub : (A : Set X) ⊆ closure A := subset_closure
  -- Monotonicity of `interior` yields the desired inclusion.
  exact interior_mono hSub