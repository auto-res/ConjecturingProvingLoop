

theorem Topology.interior_union_closure_compl_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ∪ closure ((A : Set X)ᶜ) = (Set.univ : Set X) := by
  -- Express `closure (Aᶜ)` as the complement of `interior A`.
  have h : closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ := by
    simpa using Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  -- Substitute and apply the union–complement law.
  calc
    interior (A : Set X) ∪ closure ((A : Set X)ᶜ)
        = interior (A : Set X) ∪ (interior (A : Set X))ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa using Set.union_compl_self (interior (A : Set X))