

theorem interior_closure_subset_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (closure A) ⊆ closure B := by
  -- `interior (closure A)` is always contained in `closure A`.
  have h₁ : interior (closure A) ⊆ closure A := interior_subset
  -- Monotonicity of `closure` turns `A ⊆ B` into `closure A ⊆ closure B`.
  have h₂ : closure A ⊆ closure B := closure_mono hAB
  -- Combine the two inclusions to obtain the desired result.
  exact Set.Subset.trans h₁ h₂