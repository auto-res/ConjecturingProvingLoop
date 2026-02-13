

theorem closure_union_interior_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A ∪ interior B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `closure A` is contained in `closure (A ∪ B)` by monotonicity of `closure`.
      have h : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact h hxA
  | inr hxB =>
      -- `interior B` is contained in `B`.
      have hxB_in_B : x ∈ B := interior_subset hxB
      -- Hence `x` belongs to `A ∪ B`.
      have hx_union : x ∈ A ∪ B := Or.inr hxB_in_B
      -- Any point of `A ∪ B` lies in its closure.
      exact subset_closure hx_union