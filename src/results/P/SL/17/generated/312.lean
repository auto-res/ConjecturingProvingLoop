

theorem Topology.frontier_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (closure (interior (closure (interior A)))) =
      frontier (closure (interior A)) := by
  -- Obtain the core set equality from idempotence of `closure ∘ interior`.
  have hEq :
      closure (interior (closure (interior A))) = closure (interior A) :=
    Topology.closure_interior_idempotent (A := A)
  -- Rewrite both frontiers using the established equality.
  simpa [frontier, hEq]