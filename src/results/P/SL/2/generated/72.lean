

theorem Topology.P2_iff_P3_of_interior_closure_interior_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : interior (closure (interior A)) = interior (closure A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    intro x hxA
    have : x ∈ interior (closure (interior A)) := hP2 hxA
    simpa [hEq] using this
  · intro hP3
    intro x hxA
    have : x ∈ interior (closure A) := hP3 hxA
    simpa [hEq] using this