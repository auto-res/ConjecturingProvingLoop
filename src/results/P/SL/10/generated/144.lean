

theorem Topology.interior_eq_univ_iff_closure_compl_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = (Set.univ : Set X) ↔ closure (Aᶜ) = (∅ : Set X) := by
  -- Core relation between the two sets
  have h_rel : closure (Aᶜ) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  constructor
  · intro hInt
    -- Substitute `interior A = univ` into the core relation
    simpa [hInt] using h_rel
  · intro hCl
    -- Use `h_rel` and the hypothesis `closure (Aᶜ) = ∅`
    have h_compl : (interior A)ᶜ = (∅ : Set X) := by
      simpa [hCl] using h_rel.symm
    -- Complement both sides to get `interior A = univ`
    have hInt : interior A = (∅ : Set X)ᶜ := by
      have := congrArg (fun s : Set X => sᶜ) h_compl
      simpa using this
    simpa using hInt