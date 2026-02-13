

theorem Topology.closure_compl_eq_compl_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (Aᶜ : Set X) = (interior (A : Set X))ᶜ := by
  -- Start from the existing relationship between `interior` and `closure` of complements.
  have h : interior (A : Set X) = (closure (Aᶜ : Set X))ᶜ :=
    Topology.interior_eq_compl_closure_compl (A := A)
  -- Taking complements on both sides yields the desired identity.
  simpa using (congrArg Set.compl h).symm