

theorem interior_closure_interior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    interior (closure (interior A)) ⊆ A := by
  -- First, `interior (closure (interior A))` is contained in `closure (interior A)`.
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  -- Next, because `A` is closed, `closure (interior A)` is contained in `A`.
  have h₂ : closure (interior A) ⊆ A :=
    closure_interior_subset_of_isClosed (X := X) (A := A) hA_closed
  -- Combining the two inclusions yields the result.
  exact Set.Subset.trans h₁ h₂