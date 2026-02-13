

theorem interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (A : Set X) := by
  -- First step: the interior of a set is contained in the set itself.
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  -- Second step: the closure operator is monotone.
  have h₂ : closure (interior A) ⊆ closure (A : Set X) := by
    apply closure_mono
    exact (interior_subset : interior A ⊆ A)
  -- Combining the two inclusions yields the desired result.
  exact Set.Subset.trans h₁ h₂