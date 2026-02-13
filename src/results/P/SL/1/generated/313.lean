

theorem Topology.dense_interior_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Dense (interior (closure A)) := by
  intro hDense
  -- Since `A` is dense, its closure is the whole space.
  have hClA : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Hence the interior of that closure is also the whole space.
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [hClA, interior_univ]
  -- Taking closures preserves this equality.
  have hClInt : closure (interior (closure A)) = (Set.univ : Set X) := by
    simpa [hInt, closure_univ]
  -- Conclude density from the closure equality.
  exact (dense_iff_closure_eq).2 hClInt