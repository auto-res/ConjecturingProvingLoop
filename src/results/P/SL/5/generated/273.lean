

theorem interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ := by
  classical
  -- Apply the complement lemma to `Aᶜ`.
  have h :=
    closure_compl_eq_compl_interior (X := X) (A := (A : Set X)ᶜ)
  -- Rewrite the complements.
  have h' : closure (A : Set X) = (interior ((A : Set X)ᶜ))ᶜ := by
    simpa [Set.compl_compl] using h
  -- Take complements of both sides to obtain the desired equality.
  have h'' : interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ := by
    simpa using (congrArg Set.compl h').symm
  exact h''