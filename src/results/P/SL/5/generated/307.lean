

theorem closure_compl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure ((A : Set X)ᶜ) ∩ interior A = (∅ : Set X) := by
  -- Apply the existing lemma to the complement set `Aᶜ`.
  have h :=
    closure_inter_interior_compl_eq_empty (X := X) (A := (Aᶜ : Set X))
  -- Rewrite the complements to match the desired statement.
  simpa [Set.compl_compl] using h