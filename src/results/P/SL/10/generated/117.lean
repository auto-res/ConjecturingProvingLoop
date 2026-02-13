

theorem Topology.interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (Aᶜ) = (closure A)ᶜ := by
  -- First, rewrite `closure A` in terms of `interior (Aᶜ)` using an existing lemma.
  have h₁ : closure A = (interior (Aᶜ))ᶜ := by
    -- Apply the lemma for the complement set `Aᶜ`.
    have h := Topology.closure_compl_eq_compl_interior (X := X) (A := Aᶜ)
    simpa [Set.compl_compl] using h
  -- Take complements of both sides of `h₁` to obtain the desired equality.
  have h₂ : interior (Aᶜ) = (closure A)ᶜ := by
    have := congrArg (fun s : Set X => sᶜ) h₁
    simpa [Set.compl_compl] using this.symm
  simpa using h₂