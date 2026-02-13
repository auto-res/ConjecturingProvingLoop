

theorem closure_interiors_union_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    (closure (interior (A : Set X)) ∪ closure (interior B)) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_subset :
          closure (interior (A : Set X)) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior (A : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact h_subset hA
  | inr hB =>
      have h_subset :
          closure (interior (B : Set X)) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior (B : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact h_subset hB