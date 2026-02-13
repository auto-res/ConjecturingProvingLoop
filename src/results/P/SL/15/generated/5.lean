

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior (closure (interior A)) ⊆ closure A := by
  open Set in
  have h₁ : closure (interior A) ⊆ closure A := closure_mono interior_subset
  have h₂ : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h₁
  exact h₂.trans interior_subset