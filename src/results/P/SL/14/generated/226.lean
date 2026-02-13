

theorem Topology.dense_iff_closureInteriorClosure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔
      closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    -- Since `A` is dense, its closure is the whole space.
    have h_closureA : closure (A : Set X) = (Set.univ : Set X) :=
      hDense.closure_eq
    -- Hence the interior of this closure is also the whole space.
    have h_int : interior (closure (A : Set X)) = (Set.univ : Set X) := by
      simpa [h_closureA] using
        (interior_univ : interior (Set.univ : Set X) = Set.univ)
    -- Taking the closure again yields the desired equality.
    simpa [h_int, closure_univ]
  · intro hEq
    -- The given equality implies that `interior (closure A)` is dense.
    have hDenseInt :
        Dense (interior (closure (A : Set X))) := by
      have : closure (interior (closure (A : Set X))) = (Set.univ : Set X) := hEq
      exact
        ((dense_iff_closure_eq
            (s := (interior (closure (A : Set X)) : Set X))).2) this
    -- Density of `interior (closure A)` implies density of `A`.
    exact
      Topology.dense_of_denseInteriorClosure
        (X := X) (A := A) hDenseInt