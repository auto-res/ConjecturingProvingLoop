

theorem Topology.closed_P1_iff_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) :
    Topology.P1 (X := X) A ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    exact Topology.closed_P1_closure_interior_eq_self (X := X) (A := A) hClosed hP1
  · intro h_eq
    -- Prove `P1` using the assumed equality
    dsimp [Topology.P1]
    intro x hxA
    have : x ∈ closure (interior A) := by
      simpa [h_eq] using hxA
    exact this