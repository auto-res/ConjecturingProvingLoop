

theorem interior_closure_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    (interior (closure (A : Set X)) ∪ interior (closure (B : Set X))) ⊆
      interior (closure (A ∪ B : Set X)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ interior (closure A)`.
      have hMono : interior (closure (A : Set X)) ⊆
          interior (closure (A ∪ B : Set X)) := by
        have hCl : closure (A : Set X) ⊆ closure (A ∪ B : Set X) :=
          closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact interior_mono hCl
      exact hMono hxA
  | inr hxB =>
      -- Handle the case `x ∈ interior (closure B)`.
      have hMono : interior (closure (B : Set X)) ⊆
          interior (closure (A ∪ B : Set X)) := by
        have hCl : closure (B : Set X) ⊆ closure (A ∪ B : Set X) :=
          closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact interior_mono hCl
      exact hMono hxB