

theorem interior_closure_union_subset_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_mono : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have : closure A ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact interior_mono this
      exact h_mono hA
  | inr hB =>
      have h_mono : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have : closure B ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact interior_mono this
      exact h_mono hB