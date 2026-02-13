

theorem Topology.P3_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) : Topology.P3 (closure A) := by
  unfold Topology.P3
  intro x hx
  -- `A` is dense, so its closure is the whole space.
  have h_closure : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Hence the interior of its closure is also the whole space.
  have h_int : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closure] using (interior_univ : interior (Set.univ : Set X) = Set.univ)
  -- Trivially, every point lies in `Set.univ`.
  have : x ∈ (Set.univ : Set X) := by
    simp
  -- Conclude using the equality for interiors.
  simpa [h_int] using this