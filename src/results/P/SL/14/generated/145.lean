

theorem Topology.denseInteriorClosure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Dense (interior (closure (A : Set X))) := by
  intro hDense
  -- From the density of `A`, we know `closure (interior (closure A)) = univ`.
  have h_closure :
      closure (interior (closure (A : Set X))) = (Set.univ : Set X) :=
    Topology.closureInteriorClosure_eq_univ_of_dense (X := X) (A := A) hDense
  -- Conclude density via the closure characterization.
  exact (dense_iff_closure_eq).2 h_closure