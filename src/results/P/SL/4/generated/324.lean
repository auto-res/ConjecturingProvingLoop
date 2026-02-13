

theorem closure_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A ∩ interior (Aᶜ) = (∅ : Set X) := by
  -- Rewrite `interior (Aᶜ)` using the complement–closure formula.
  have h : interior (Aᶜ) = (closure A)ᶜ :=
    interior_compl_eq_compl_closure (A := A)
  -- The intersection of a set with its complement is empty.
  simpa [h] using (Set.inter_compl_self (closure A))