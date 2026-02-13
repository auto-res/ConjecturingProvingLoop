

theorem interior_complement_eq_complement_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior ((Aᶜ) : Set X) = (closure (A : Set X))ᶜ := by
  -- Apply the existing lemma to the complement of `A`
  have h : closure (A : Set X) = (interior ((Aᶜ) : Set X))ᶜ := by
    simpa [Set.compl_compl] using
      (closure_compl_eq_complement_interior (A := (Aᶜ : Set X)))
  -- Take complements of both sides to obtain the desired equality
  have h' : interior ((Aᶜ) : Set X) = (closure (A : Set X))ᶜ := by
    have := congrArg Set.compl h
    simpa [Set.compl_compl] using this.symm
  exact h'