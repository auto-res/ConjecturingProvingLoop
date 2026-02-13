

theorem Topology.P2_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P2 (closure (A : Set X)) := by
  intro hDense
  -- Since `A` is dense, its closure is the whole space, which is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have h_eq : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
    simpa [h_eq] using (isOpen_univ : IsOpen (Set.univ : Set X))
  -- Apply the lemma that an open closure guarantees `P2`.
  exact (Topology.P2_of_isOpen_closure (X := X) (A := A)) hOpen