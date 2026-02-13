

theorem Topology.frontier_closure_eq_closure_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (closure (A : Set X)) =
      closure (A : Set X) \ interior (closure (A : Set X)) := by
  -- By definition, `frontier S = closure S \ interior S`.  Applying this
  -- with `S = closure A` and simplifying the redundant `closure` yields
  -- the desired identity.
  simp [frontier, closure_closure]