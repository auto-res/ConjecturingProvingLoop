

theorem Topology.interior_compl_union_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ : Set X) ∪ closure (A : Set X) = (Set.univ : Set X) := by
  -- Rewrite `interior (Aᶜ)` as the complement of `closure A`.
  have h : interior (Aᶜ : Set X) = (closure (A : Set X))ᶜ := by
    simpa using
      (Topology.interior_compl_eq_compl_closure (X := X) (A := A))
  -- Use the complement law `sᶜ ∪ s = univ`.
  calc
    interior (Aᶜ : Set X) ∪ closure (A : Set X)
        = (closure (A : Set X))ᶜ ∪ closure A := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simp