

theorem P2_iff_P3_of_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hEq : closure A = closure (interior A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 hP2
  · intro hP3
    dsimp [Topology.P2] at *
    dsimp [Topology.P3] at hP3
    intro x hx
    have hx' : x ∈ interior (closure A) := hP3 hx
    have hIntEq : interior (closure A) = interior (closure (interior A)) := by
      simpa [hEq]
    simpa [hIntEq] using hx'