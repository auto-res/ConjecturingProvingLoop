

theorem interior_subset_closure_of_subset_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} (h : B ⊆ closure A) :
    interior B ⊆ closure A := by
  intro x hx
  have hxB : x ∈ B := interior_subset hx
  exact h hxB