

theorem closure_union_interior_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) ⊆ closure (interior (A ∪ B)) := by
  open Set in
  have h_subset : interior A ∪ interior B ⊆ interior (A ∪ B) := by
    intro x hx
    cases hx with
    | inl hA =>
        have hMono : interior A ⊆ interior (A ∪ B) :=
          interior_mono (subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact hMono hA
    | inr hB =>
        have hMono : interior B ⊆ interior (A ∪ B) :=
          interior_mono (subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact hMono hB
  exact closure_mono h_subset