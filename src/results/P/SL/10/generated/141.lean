

theorem Topology.closure_eq_compl_interior_compl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A = (interior (Aᶜ))ᶜ := by
  have h := Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  have h' := congrArg (fun s : Set X => sᶜ) h
  simpa [Set.compl_compl] using h'.symm