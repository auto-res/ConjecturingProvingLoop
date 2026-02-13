

theorem Topology.closure_interior_eq_of_closed_and_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    closure (interior A) = A := by
  -- First, `A` is open because it is closed and satisfies `P3`.
  have hA_open : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  -- Hence the interior of `A` is `A` itself.
  have h_int : interior A = A := hA_open.interior_eq
  -- Rewrite `closure (interior A)` using the above equality and use that `A` is closed.
  calc
    closure (interior A) = closure A := by
      simpa [h_int]
    _ = A := hA_closed.closure_eq