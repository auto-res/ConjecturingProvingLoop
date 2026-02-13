

theorem Topology.P3_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P3 (closure (A : Set X)) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  -- Since `A` is dense, its closure is the whole space.
  have h_closure_eq : closure (A : Set X) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Hence every point lies in the interior of this closure (and of its
  -- further closure, which is equal to itself).
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [closure_closure, h_closure_eq, interior_univ] using this