

theorem closure_union_closure_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∪ B : Set X) = closure (A ∪ B) := by
  apply subset_antisymm
  ·
    -- Show `closure (closure A ∪ B)` is contained in `closure (A ∪ B)`.
    have hSub : (closure A ∪ B : Set X) ⊆ closure (A ∪ B) := by
      intro x hx
      cases hx with
      | inl hClA =>
          have : closure A ⊆ closure (A ∪ B) :=
            closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
          exact this hClA
      | inr hB =>
          exact subset_closure (Or.inr hB)
    have : closure (closure A ∪ B) ⊆ closure (closure (A ∪ B)) :=
      closure_mono hSub
    simpa [closure_closure] using this
  ·
    -- Show `closure (A ∪ B)` is contained in `closure (closure A ∪ B)`.
    have hSub : (A ∪ B : Set X) ⊆ closure A ∪ B := by
      intro x hx
      cases hx with
      | inl hA   => exact Or.inl (subset_closure hA)
      | inr hB   => exact Or.inr hB
    exact closure_mono hSub