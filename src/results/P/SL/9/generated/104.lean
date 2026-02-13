

theorem Topology.interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ) = (closure A)ᶜ := by
  classical
  -- Start from the known relation with `Aᶜ`.
  have h := Topology.closure_compl_eq_compl_interior (A := Aᶜ)
  -- `h : closure A = (interior (Aᶜ))ᶜ`
  -- Take complements of both sides.
  have h' := congrArg (fun s : Set X => sᶜ) h
  -- Rearrange and simplify double complements.
  simpa [compl_compl] using h'.symm