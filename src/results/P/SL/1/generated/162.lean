

theorem Topology.closure_interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense A) :
    closure (interior (closure A)) = (Set.univ : Set X) := by
  -- Since `A` is dense, its closure is the whole space.
  have hclosure : closure A = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- Rewriting with this equality simplifies the goal to a tautology.
  simpa [hclosure, interior_univ, closure_univ]