

theorem P1_iff_P2_of_closed_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosedInt : IsClosed (interior A)) :
    Topology.P1 A ↔ Topology.P2 A := by
  -- `closure (interior A)` collapses to `interior A` because this interior is closed.
  have hClosEq : closure (interior A) = interior A := hClosedInt.closure_eq
  constructor
  · intro hP1
    dsimp [Topology.P2] at *
    intro x hxA
    -- From `P1`, `x` lies in `closure (interior A) = interior A`.
    have hxIntA : x ∈ interior A := by
      have hxClos : x ∈ closure (interior A) := hP1 hxA
      simpa [hClosEq] using hxClos
    -- Re-interpret this membership in the desired interior.
    simpa [hClosEq, interior_interior] using hxIntA
  · intro hP2
    dsimp [Topology.P1] at *
    intro x hxA
    -- `P2` gives `x` in `interior (closure (interior A))`.
    have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
    -- The interior is contained in the closure.
    have hIncl : interior (closure (interior A))
        ⊆ closure (interior A) := interior_subset
    exact hIncl hxInt