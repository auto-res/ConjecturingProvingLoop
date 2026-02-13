

theorem Topology.closureInteriorClosure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense (A : Set X)) :
    closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
  -- Since `A` is dense, its closure is the whole space.
  have h_closure : closure (A : Set X) = (Set.univ : Set X) := hA.closure_eq
  -- Hence the interior of that closure is also `univ`.
  have h_int : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [h_closure, interior_univ]
  -- Taking the closure once more leaves the set unchanged.
  calc
    closure (interior (closure (A : Set X)))
        = closure (Set.univ : Set X) := by
          simpa [h_int]
    _ = (Set.univ : Set X) := by
          simpa [closure_univ]