

theorem frontier_eq_empty_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) :
    frontier (A : Set X) = (∅ : Set X) := by
  classical
  -- In a discrete space, every set is both closed and open.
  have h_closure : closure (A : Set X) = A := (isClosed_discrete _).closure_eq
  have h_interior : interior (A : Set X) = A := (isOpen_discrete _).interior_eq
  -- Hence the frontier, defined as `closure A \ interior A`, is empty.
  simp [frontier, h_closure, h_interior, Set.diff_self]