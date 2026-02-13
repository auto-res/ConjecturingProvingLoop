

theorem union_interior_closure_and_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ∪ closure (interior A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl hxInt =>
      exact (interior_subset : interior (closure (A : Set X)) ⊆ closure A) hxInt
  | inr hxCl =>
      -- `interior A ⊆ A`, so their closures satisfy the same inclusion.
      have hSub : interior (A : Set X) ⊆ A := interior_subset
      have hClSub : closure (interior (A : Set X)) ⊆ closure A :=
        closure_mono hSub
      exact hClSub hxCl