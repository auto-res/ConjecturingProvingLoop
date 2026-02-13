

theorem P1_iff_closure_interior_eq_self_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P1 (X := X) A ↔ closure (interior A) = A := by
  -- Rewrite `closure A` using the closedness of `A`.
  have h_closure_eq : closure (A : Set X) = A := hA_closed.closure_eq
  -- Use the existing characterization of `P1`.
  have h :=
    Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)
  -- Substitute `closure A = A` in the equivalence and adjust the equality orientation.
  simpa [h_closure_eq, eq_comm] using h