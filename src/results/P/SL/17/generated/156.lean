

theorem Topology.closure_interior_compl_eq_compl_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (Aᶜ)) = (interior (closure A))ᶜ := by
  -- Start with the known relation for complements of closures of interiors.
  have h :
      (closure (interior (Aᶜ)))ᶜ = interior (closure A) := by
    simpa [compl_compl] using
      (Topology.compl_closure_interior_eq_interior_closure_compl (A := Aᶜ))
  -- Take complements of both sides of the equality `h`.
  have h' :
      ((closure (interior (Aᶜ)))ᶜ)ᶜ = (interior (closure A))ᶜ :=
    congrArg Set.compl h
  -- Simplify double complements to obtain the desired statement.
  simpa [compl_compl] using h'