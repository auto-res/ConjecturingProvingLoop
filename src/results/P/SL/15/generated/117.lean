

theorem P1_and_dense_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Dense A → Topology.P2 A := by
  intro hP1 hDense
  dsimp [Topology.P2]
  intro x hx
  -- From `P1` and density we know `closure (interior A)` is the whole space.
  have h_closure_univ :
      closure (interior A) = (Set.univ : Set X) :=
    Topology.closure_interior_eq_univ_of_P1_and_dense
      (X := X) (A := A) hP1 hDense
  -- Hence its interior is also the whole space.
  have h_int_univ :
      interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [h_closure_univ, interior_univ]
  -- Conclude the desired membership.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_int_univ] using this