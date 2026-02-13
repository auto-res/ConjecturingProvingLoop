

theorem Topology.dense_iff_eq_univ_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Dense (A : Set X) ↔ (A : Set X) = Set.univ := by
  have h_closure : closure (A : Set X) = A := hA_closed.closure_eq
  have h_dense :
      Dense (A : Set X) ↔ closure (A : Set X) = (Set.univ : Set X) :=
    dense_iff_closure_eq (s := (A : Set X))
  simpa [h_closure] using h_dense