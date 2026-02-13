

theorem union_closure_eq_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    (A ∪ closure A : Set X) = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hA   => exact subset_closure hA
    | inr hClA => exact hClA
  · intro x hx
    exact Or.inr hx