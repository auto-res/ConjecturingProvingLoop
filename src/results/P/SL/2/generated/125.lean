

theorem Topology.isClosed_P2_iff_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → (Topology.P2 A ↔ interior A = A) := by
  intro hClosed
  constructor
  · intro hP2
    exact Topology.isClosed_P2_implies_interior_eq_self (A := A) hClosed hP2
  · intro hIntEq
    -- From `interior A = A`, we obtain that `A` is open.
    have hOpen : IsOpen A := (isOpen_iff_interior_eq (A := A)).2 hIntEq
    -- Any open set satisfies `P2`.
    exact Topology.isOpen_implies_P2 (A := A) hOpen