

theorem Topology.closure_interior_compl_eq_compl_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (Aᶜ)) = (interior (closure A))ᶜ := by
  -- First rewrite `interior (Aᶜ)` using an existing complement–closure lemma.
  have h₁ : interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  -- Apply the closure–interior complement lemma to `closure A`.
  have h₂ : closure ((closure A)ᶜ) = (interior (closure A))ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := closure A)
  -- Combine the two equalities.
  simpa [h₁] using h₂