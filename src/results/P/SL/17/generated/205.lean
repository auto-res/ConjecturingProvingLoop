

theorem Topology.frontier_eq_empty_of_discrete {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] {A : Set X} :
    frontier A = (∅ : Set X) := by
  -- In a discrete topology every set is open, hence its interior is itself.
  have hInt : interior A = A := (isOpen_discrete _).interior_eq
  -- Likewise, every set is closed, so its closure is itself.
  have hClos : closure A = A := by
    have hClosed : IsClosed A := isClosed_discrete _
    simpa using hClosed.closure_eq
  -- Substituting these equalities into the definition of `frontier`
  -- yields the empty set.
  simp [frontier, hInt, hClos, Set.diff_self]