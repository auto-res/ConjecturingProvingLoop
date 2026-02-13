

theorem closure_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A ∪ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hIncl : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hIncl hA
  | inr hB =>
      have hIncl : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hIncl hB