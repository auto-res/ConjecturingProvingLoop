

theorem closure_union_interior_closure_eq_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A ∪ interior (closure A) = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl h₁ => exact h₁
    | inr h₂ =>
        exact (interior_subset : interior (closure A) ⊆ closure A) h₂
  · intro x hx
    exact Or.inl hx