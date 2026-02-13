

theorem Topology.closure_eq_univ_iff_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) ↔
      interior (Aᶜ : Set X) = (∅ : Set X) := by
  -- `closure A = univ` is equivalent to `Dense A`.
  have h₁ :
      closure (A : Set X) = (Set.univ : Set X) ↔ Dense (A : Set X) :=
    (dense_iff_closure_eq (s := (A : Set X))).symm
  -- `Dense A` is equivalent to `interior (Aᶜ) = ∅`.
  have h₂ :
      Dense (A : Set X) ↔ interior (Aᶜ : Set X) = (∅ : Set X) :=
    Topology.dense_iff_interior_compl_eq_empty (X := X) (A := A)
  -- Combine the two equivalences.
  simpa using h₁.trans h₂