

theorem closure_interior_union_closure_eq_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∪ closure A = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl h₁ =>
        have h_subset : closure (interior A) ⊆ closure A :=
          closure_interior_subset_closure (X := X) (A := A)
        exact h_subset h₁
    | inr h₂ =>
        exact h₂
  · intro x hx
    exact Or.inr hx