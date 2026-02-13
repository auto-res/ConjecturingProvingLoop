

theorem closure_interior_union_subset_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ interior B) ⊆ closure (A ∪ B) := by
  -- First, show the underlying inclusion without the closures.
  have hSub : (interior (A : Set X) ∪ interior B) ⊆ A ∪ B := by
    intro x hx
    cases hx with
    | inl hA =>
        exact Or.inl ((interior_subset : interior (A : Set X) ⊆ A) hA)
    | inr hB =>
        exact Or.inr ((interior_subset : interior (B : Set X) ⊆ B) hB)
  -- The `closure` operator is monotone, so the desired inclusion follows.
  exact closure_mono hSub