

theorem Topology.closure_eq_univ_iff_interiorClosure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) ↔
      interior (closure A) = (Set.univ : Set X) := by
  constructor
  · intro h_closure
    -- Rewrite using `h_closure` and `interior_univ`.
    have : interior (closure (A : Set X)) = interior (Set.univ : Set X) := by
      simpa [h_closure]
    simpa [interior_univ] using this
  · intro h_int
    -- From `interior (closure A) = univ` we get `univ ⊆ closure A`.
    have h_subset₁ : (Set.univ : Set X) ⊆ closure A := by
      have : interior (closure A) ⊆ closure A := interior_subset
      simpa [h_int] using this
    -- The opposite inclusion is trivial.
    have h_subset₂ : closure (A : Set X) ⊆ (Set.univ : Set X) := by
      intro x hx; simp
    exact Set.Subset.antisymm h_subset₂ h_subset₁