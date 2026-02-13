

theorem closure_union_closure_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∪ closure B) = closure (A ∪ B) := by
  apply subset_antisymm
  ·
    -- First inclusion: `closure (A ∪ closure B) ⊆ closure (A ∪ B)`.
    have hSub : (A ∪ closure B : Set X) ⊆ closure (A ∪ B) := by
      intro x hx
      cases hx with
      | inl hA =>
          -- `x ∈ A`, hence `x ∈ closure (A ∪ B)` by closure monotonicity.
          exact subset_closure (Or.inl hA)
      | inr hClB =>
          -- `x ∈ closure B`, and `closure B ⊆ closure (A ∪ B)`.
          have : closure B ⊆ closure (A ∪ B) :=
            closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
          exact this hClB
    have : closure (A ∪ closure B) ⊆ closure (closure (A ∪ B)) :=
      closure_mono hSub
    simpa [closure_closure] using this
  ·
    -- Second inclusion: `closure (A ∪ B) ⊆ closure (A ∪ closure B)`.
    have hSub : (A ∪ B : Set X) ⊆ A ∪ closure B := by
      intro x hx
      cases hx with
      | inl hA => exact Or.inl hA
      | inr hB => exact Or.inr (subset_closure hB)
    exact (closure_mono hSub)