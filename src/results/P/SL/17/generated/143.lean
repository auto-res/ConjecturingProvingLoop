

theorem Topology.P3_closure_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : Topology.P3 (closure A) := by
  unfold Topology.P3
  intro x hx
  -- `interior (closure A)` is the whole space because `interior A` is dense.
  have hInt : interior (closure A) = (Set.univ : Set X) :=
    Topology.interior_closure_eq_univ_of_dense_interior (A := A) hDense
  -- Therefore every point belongs to `interior (closure A)`.
  have hxInt : x ∈ interior (closure A) := by
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hInt] using this
  -- Rewrite to obtain membership in `interior (closure (closure A))`.
  simpa [closure_closure] using hxInt