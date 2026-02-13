

theorem closure_union_eq_union_closure {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure ((A ∪ B) : Set X) = closure (A : Set X) ∪ closure (B : Set X) := by
  apply Set.Subset.antisymm
  · -- `closure (A ∪ B) ⊆ closure A ∪ closure B`
    have h_subset : (A ∪ B : Set X) ⊆ closure (A : Set X) ∪ closure (B : Set X) := by
      intro x hx
      cases hx with
      | inl hA => exact Or.inl (subset_closure hA)
      | inr hB => exact Or.inr (subset_closure hB)
    have h_closed : IsClosed (closure (A : Set X) ∪ closure (B : Set X)) :=
      (isClosed_closure).union isClosed_closure
    exact closure_minimal h_subset h_closed
  · -- `closure A ∪ closure B ⊆ closure (A ∪ B)`
    intro x hx
    cases hx with
    | inl hA =>
        have h : closure (A : Set X) ⊆ closure ((A ∪ B) : Set X) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact h hA
    | inr hB =>
        have h : closure (B : Set X) ⊆ closure ((A ∪ B) : Set X) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact h hB