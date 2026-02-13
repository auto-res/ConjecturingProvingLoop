

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  have h₁ : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_closure_interior_subset (A := A)
  have h₂ : interior (closure A) ⊆ closure A := interior_subset
  exact h₁.trans h₂