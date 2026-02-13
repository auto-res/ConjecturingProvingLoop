

theorem Topology.closure_interior_eq_of_closed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = A := by
  -- First, `interior A` coincides with `A` under the given assumptions.
  have h_int : interior A = A :=
    Topology.interior_eq_self_of_closed_and_P2 (A := A) hA_closed hP2
  -- Rewrite `closure (interior A)` using the above equality
  -- and use that `A` is closed.
  calc
    closure (interior A) = closure A := by
      simpa [h_int]
    _ = A := hA_closed.closure_eq