

theorem Topology.closure_has_P3_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 (closure A) := by
  intro hDense
  -- The closure of `interior A` is the whole space.
  have h_closureInt : closure (interior A) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Hence `closure A` is also the whole space.
  have h_closureA_univ : closure (A : Set X) = (Set.univ : Set X) := by
    -- `closure (interior A)` is contained in `closure A`.
    have h_sub : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    -- Using `h_closureInt`, this means `univ ⊆ closure A`.
    have h_subset : (Set.univ : Set X) ⊆ closure A := by
      simpa [h_closureInt] using h_sub
    -- The reverse inclusion is trivial.
    have h_superset : closure A ⊆ (Set.univ : Set X) := by
      intro x hx; simp
    exact Set.Subset.antisymm h_superset h_subset
  -- Since `closure A = univ`, it is open, so it satisfies `P3`.
  have h_open : IsOpen (closure A) := by
    simpa [h_closureA_univ] using (isOpen_univ : IsOpen (Set.univ : Set X))
  exact Topology.isOpen_implies_P3 (X := X) (A := closure A) h_open