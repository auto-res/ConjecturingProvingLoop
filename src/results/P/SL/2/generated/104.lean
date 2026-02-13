

theorem Topology.P1_iff_P3_of_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : interior (closure (A : Set X)) = closure (interior A)) :
    Topology.P1 A ↔ Topology.P3 A := by
  constructor
  · intro hP1
    intro x hxA
    have hx : x ∈ closure (interior A) := hP1 hxA
    simpa [hEq.symm] using hx
  · intro hP3
    intro x hxA
    have hx : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [hEq] using hx