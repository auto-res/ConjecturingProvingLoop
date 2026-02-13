

theorem Topology.closure_interior_closure_eq_univ_of_dense {X : Type*}
    [TopologicalSpace X] {A : Set X} (hDense : Dense A) :
    closure (interior (closure A)) = (Set.univ : Set X) := by
  -- Since `A` is dense, its closure is the whole space.
  have h_closure : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Consequently, the interior of its closure is also the whole space.
  have h_int : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closure] using interior_univ
  -- Taking the closure again yields the whole space.
  calc
    closure (interior (closure A))
        = closure (Set.univ : Set X) := by
          simpa [h_int]
    _ = (Set.univ : Set X) := by
          simpa using closure_univ