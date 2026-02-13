

theorem Topology.P2_closure_of_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P2 (closure A) := by
  intro hP3
  -- Since `closure A` is closed, `P3` implies it is open.
  have hOpen : IsOpen (closure A) := by
    have hClosed : IsClosed (closure A) := isClosed_closure
    exact (Topology.isOpen_of_P3_of_isClosed (A := closure A) hClosed) hP3
  -- Any open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := closure A) hOpen