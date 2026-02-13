

theorem closure_union_interiors_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((interior (A : Set X)) ∪ interior B) ⊆ closure (interior (A ∪ B)) := by
  have h_subset : (interior (A : Set X) ∪ interior B) ⊆ interior (A ∪ B) := by
    intro x hx
    cases hx with
    | inl hA =>
        have hA_subset : interior (A : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact hA_subset hA
    | inr hB =>
        have hB_subset : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact hB_subset hB
  exact closure_mono h_subset