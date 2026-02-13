

theorem interior_closure_interior_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (interior (A : Set X))) ∪
        interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_closure : closure (interior (A : Set X))
          ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have h_int : interior (A : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact h_int
      exact (interior_mono h_closure) hA
  | inr hB =>
      have h_closure : closure (interior (B : Set X))
          ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have h_int : interior (B : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact h_int
      exact (interior_mono h_closure) hB