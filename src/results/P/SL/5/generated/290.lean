

theorem closure_union_interior_compl_eq_univ
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∪ interior ((A : Set X)ᶜ) = (Set.univ : Set X) := by
  classical
  -- Rewrite `interior (Aᶜ)` as the complement of `closure A`.
  have h : interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ :=
    interior_compl_eq_compl_closure (X := X) (A := A)
  -- Use this equality and the fact that a set union its complement is `univ`.
  calc
    closure (A : Set X) ∪ interior ((A : Set X)ᶜ)
        = closure (A : Set X) ∪ (closure (A : Set X))ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa using Set.union_compl_self (closure (A : Set X))