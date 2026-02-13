

theorem Topology.isOpen_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (A : Set X)) : IsOpen A := by
  -- From density and closedness we get `A = univ`.
  have h_eq : (A : Set X) = (Set.univ : Set X) :=
    ((Topology.dense_iff_eq_univ_of_isClosed (X := X) (A := A) hA_closed).1)
      hDense
  -- The universe is open.
  simpa [h_eq] using (isOpen_univ : IsOpen (Set.univ : Set X))