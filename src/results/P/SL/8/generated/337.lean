

theorem closure_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ interior (Aᶜ) = (∅ : Set X) := by
  -- Rewrite `interior (Aᶜ)` as the complement of `closure A`.
  have h : interior (Aᶜ) = (closure A)ᶜ :=
    interior_compl_eq_compl_closure (X := X) (A := A)
  calc
    closure A ∩ interior (Aᶜ)
        = closure A ∩ (closure A)ᶜ := by
          simpa [h]
    _ = (∅ : Set X) := by
          simpa using Set.inter_compl_self (closure A)