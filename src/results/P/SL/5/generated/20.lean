

theorem interior_closure_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hsubset : closure (A : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact (interior_mono hsubset) hxA
  | inr hxB =>
      have hsubset : closure (B : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact (interior_mono hsubset) hxB