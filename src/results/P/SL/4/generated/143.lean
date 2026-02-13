

theorem closure_interior_union_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∪ interior (closure A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl h₁ =>
      exact closure_interior_subset_closure (X := X) (A := A) h₁
  | inr h₂ =>
      exact interior_closure_subset_closure (X := X) (A := A) h₂