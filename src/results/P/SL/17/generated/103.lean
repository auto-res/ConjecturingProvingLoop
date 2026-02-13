

theorem Topology.interior_closure_interior_closure_eq_univ_of_dense {X : Type*}
    [TopologicalSpace X] {A : Set X} (hDense : Dense A) :
    interior (closure (interior (closure A))) = (Set.univ : Set X) := by
  -- First, `interior (closure A)` is the whole space because `A` is dense.
  have h_int : interior (closure A) = (Set.univ : Set X) :=
    Topology.interior_closure_eq_univ_of_dense (A := A) hDense
  -- Consequently, its closure is also the whole space.
  have h_closure : closure (interior (closure A)) = (Set.univ : Set X) := by
    simpa [h_int] using (closure_univ : closure (Set.univ : Set X) = Set.univ)
  -- Taking the interior again still yields the whole space.
  simpa [h_closure] using (interior_univ : interior (Set.univ : Set X) = Set.univ)