

theorem Topology.P3_of_interiorClosure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = (Set.univ : Set X) → Topology.P3 A := by
  intro hIntUniv
  -- From `interior (closure A) = univ` we deduce `closure A = univ`.
  have hClosureUniv : closure (A : Set X) = (Set.univ : Set X) := by
    -- `interior (closure A)` is contained in `closure A`.
    have hSubset : (Set.univ : Set X) ⊆ closure A := by
      have hIntSubset : interior (closure (A : Set X)) ⊆ closure A :=
        interior_subset
      simpa [hIntUniv] using hIntSubset
    -- The reverse inclusion is trivial.
    have hSuperset : closure (A : Set X) ⊆ (Set.univ : Set X) := by
      intro x _; simp
    exact Set.Subset.antisymm hSuperset hSubset
  -- Since `closure A = univ`, it is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    simpa [hClosureUniv] using (isOpen_univ : IsOpen (Set.univ : Set X))
  -- Apply the existing lemma to obtain `P3 A`.
  exact
    Topology.P3_of_isOpen_closure (X := X) (A := A) hOpen