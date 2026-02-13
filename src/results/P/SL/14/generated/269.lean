

theorem Topology.P1_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (A : Set X)) :
    Topology.P1 A := by
  -- Since `A` is dense, its closure is the whole space.
  have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- But `A` is closed, so `closure A = A`, hence `A = univ`.
  have hA_univ : (A : Set X) = Set.univ := by
    simpa [hA_closed.closure_eq] using h_closure
  -- The universe satisfies `P1`, and rewriting via `hA_univ` concludes the proof.
  simpa [hA_univ] using (Topology.P1_univ (X := X))