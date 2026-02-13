

theorem interior_inter_closure_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∩ closure (Aᶜ) = (∅ : Set X) := by
  -- `closure (Aᶜ)` is the complement of `interior A`.
  have h : closure (Aᶜ) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (X := X) (A := A)
  -- Rewrite and simplify the intersection.
  simpa [h, Set.inter_compl_self]