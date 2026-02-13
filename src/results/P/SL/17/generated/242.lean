

theorem Topology.closure_interior_closure_eq_self_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    closure (interior (closure A)) = A := by
  -- In a discrete topology every set is closed, hence `closure A = A`.
  have hClosure : closure A = (A : Set X) := by
    have hClosed : IsClosed A := isClosed_discrete _
    simpa using hClosed.closure_eq
  -- Rewriting with `hClosure` reduces the statement to the known lemma.
  calc
    closure (interior (closure A)) = closure (interior A) := by
      simpa [hClosure]
    _ = A := by
      simpa using Topology.closure_interior_eq_self_of_discrete (A := A)