

theorem dense_interior_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P2 A := by
  intro hDense
  dsimp [Topology.P2]
  intro x hxA
  -- Since `interior A` is dense, its closure is `univ`.
  have h_closure : (closure (interior A) : Set X) = Set.univ := hDense.closure_eq
  -- Hence the interior of this closure is also `univ`.
  have h_int : interior (closure (interior A)) = (Set.univ : Set X) := by
    have h_univ : interior (Set.univ : Set X) = (Set.univ : Set X) := by
      simpa using (isOpen_univ : IsOpen (Set.univ : Set X)).interior_eq
    simpa [h_closure] using h_univ
  -- Every point lies in `univ`, so the desired inclusion holds.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_int] using this