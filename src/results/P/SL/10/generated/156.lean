

theorem Topology.interior_compl_eq_univ_iff_closure_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ) = (Set.univ : Set X) ↔ closure A = (∅ : Set X) := by
  -- Relate the two sets using the existing complement–closure lemma.
  have h_rel := Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  constructor
  · intro hInt
    -- Translate `hInt` via `h_rel` to obtain `(closure A)ᶜ = univ`.
    have h_eq : (closure A)ᶜ = (Set.univ : Set X) := by
      simpa [h_rel] using hInt
    -- Complement both sides to deduce `closure A = ∅`.
    have h_closure : closure A = (Set.univ : Set X)ᶜ := by
      simpa using congrArg (fun s : Set X => sᶜ) h_eq
    simpa [Set.compl_univ] using h_closure
  · intro hCl
    -- Rewrite `interior (Aᶜ)` using `h_rel` and `hCl`.
    have h_eq : interior (Aᶜ) = (closure A)ᶜ := h_rel
    simpa [hCl, Set.compl_empty] using h_eq