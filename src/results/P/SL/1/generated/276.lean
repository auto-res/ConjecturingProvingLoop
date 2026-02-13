

theorem Topology.closure_interior_closure_interior_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (interior A)) :
    closure (interior (closure (interior A))) = (Set.univ : Set X) := by
  -- Since `interior A` is dense, its closure is the whole space.
  have h1 : closure (interior A) = (Set.univ : Set X) := h.closure_eq
  -- Rewriting with `h1` and using the facts that both `interior` and `closure`
  -- of `univ` yield `univ`, we obtain the desired equality.
  simpa [h1, interior_univ, closure_univ]