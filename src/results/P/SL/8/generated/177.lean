

theorem interior_closure_interior_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  -- First, `interior (closure (interior A)) ⊆ interior (closure A)`.
  have h₁ :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_closure_interior_subset_interior_closure (X := X) (A := A)
  -- Second, `interior (closure A) ⊆ closure (interior (closure A))`.
  have h₂ :
      interior (closure A) ⊆ closure (interior (closure A)) :=
    interior_closure_subset_closureInteriorClosure (X := X) (A := A)
  -- Composing the two inclusions yields the desired result.
  exact Set.Subset.trans h₁ h₂