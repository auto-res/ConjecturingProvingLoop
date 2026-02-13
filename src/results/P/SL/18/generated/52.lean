

theorem P1_iff_P3_of_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : interior (closure A) = closure (interior A)) :
    Topology.P1 A ↔ Topology.P3 A := by
  constructor
  · intro hP1
    dsimp [Topology.P1] at hP1
    dsimp [Topology.P3]
    intro x hx
    have hx' : x ∈ closure (interior A) := hP1 hx
    simpa [hEq] using hx'
  · intro hP3
    dsimp [Topology.P3] at hP3
    dsimp [Topology.P1]
    intro x hx
    have hx' : x ∈ interior (closure A) := hP3 hx
    simpa [hEq] using hx'