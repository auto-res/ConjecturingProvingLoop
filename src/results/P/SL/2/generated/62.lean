

theorem Topology.isClosed_P1_iff_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → (Topology.P1 A ↔ closure (interior A) = A) := by
  intro hClosed
  constructor
  · intro hP1
    exact
      Topology.isClosed_P1_implies_closure_interior_eq_self (A := A) hClosed hP1
  · intro hEq
    -- Since `A` is closed, `closure A = A`.
    have hClosure : closure (A : Set X) = A := hClosed.closure_eq
    -- Rewrite the given equality to match the characterisation of `P1`.
    have hEq' : closure (interior A) = closure A := by
      simpa [hClosure] using hEq
    -- Apply the equivalence `P1 A ↔ closure (interior A) = closure A`.
    exact
      (Topology.P1_iff_closure_interior_eq_closure (A := A)).mpr hEq'