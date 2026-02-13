

theorem interior_closure_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hIncl : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have hSub : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact closure_mono hSub
      exact hIncl hxA
  | inr hxB =>
      have hIncl : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have hSub : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact closure_mono hSub
      exact hIncl hxB