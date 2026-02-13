

theorem interior_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ⊆ closure (A : Set X) := by
  intro x hxInt
  -- From `x ∈ interior A` we infer `x ∈ A`.
  have hxA : x ∈ (A : Set X) := interior_subset hxInt
  -- The set `A` is contained in its closure.
  have : (A : Set X) ⊆ closure (A : Set X) := subset_closure
  -- Therefore, `x ∈ closure A`.
  exact this hxA