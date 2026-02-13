

theorem Topology.interior_eq_compl_closure_compl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A = (closure (Aᶜ : Set X))ᶜ := by
  -- Start with `closure (Aᶜ) = (interior A)ᶜ`.
  have h : closure (Aᶜ : Set X) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  -- Complement both sides to relate to `interior A`.
  have h' : (closure (Aᶜ : Set X))ᶜ = interior A := by
    simpa [Set.compl_compl] using congrArg (fun s : Set X => sᶜ) h
  -- Rearrange to obtain the desired equality.
  simpa [Set.compl_compl] using h'.symm