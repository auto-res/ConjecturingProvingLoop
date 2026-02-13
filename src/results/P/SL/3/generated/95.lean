

theorem closure_union_interiors_eq_union_closure_interiors
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    closure ((interior (A : Set X)) ∪ interior B) =
      closure (interior A) ∪ closure (interior B) := by
  -- We prove the equality by showing mutual inclusion.
  apply Set.Subset.antisymm
  · -- First, `closure (U ∪ V)` is contained in `closure U ∪ closure V`.
    have h_subset :
        (interior (A : Set X) ∪ interior B) ⊆
          closure (interior A) ∪ closure (interior B) := by
      intro x hx
      cases hx with
      | inl hA =>
          exact Or.inl (subset_closure hA)
      | inr hB =>
          exact Or.inr (subset_closure hB)
    have h_closed :
        IsClosed (closure (interior A) ∪ closure (interior B)) := by
      exact (isClosed_closure).union isClosed_closure
    exact closure_minimal h_subset h_closed
  · -- Conversely, each of the two closures lies inside `closure (U ∪ V)`.
    intro x hx
    cases hx with
    | inl hA =>
        have h_sub :
            closure (interior A) ⊆
              closure ((interior (A : Set X)) ∪ interior B) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact h_sub hA
    | inr hB =>
        have h_sub :
            closure (interior B) ⊆
              closure ((interior (A : Set X)) ∪ interior B) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact h_sub hB