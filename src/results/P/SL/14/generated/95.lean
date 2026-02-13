

theorem Topology.closureInteriorClosure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) →
      closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
  intro hDense
  -- Since `A` is dense, its closure is the whole space.
  have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Hence the interior of this closure is also the whole space.
  have h_int : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [h_closure, interior_univ]
  -- Taking the closure again yields the whole space.
  simpa [h_int, closure_univ]