

theorem interior_union_closure_compl_eq_univ
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ closure ((A : Set X)ᶜ) = (Set.univ : Set X) := by
  classical
  -- Rewrite `closure (Aᶜ)` using the complement of an interior.
  have h : closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ := by
    simpa using closure_compl_eq_compl_interior (X := X) (A := A)
  -- The desired equality is now immediate.
  calc
    interior (A : Set X) ∪ closure ((A : Set X)ᶜ)
        = interior (A : Set X) ∪ (interior (A : Set X))ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa using Set.union_compl_self (interior (A : Set X))