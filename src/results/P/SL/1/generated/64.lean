

theorem Topology.P2_of_P3_and_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hEq : closure A = closure (interior A)) :
    Topology.P2 A := by
  dsimp [Topology.P2, Topology.P3] at hP3 ⊢
  intro x hx
  have hxInt : x ∈ interior (closure A) := hP3 hx
  have hIntEq : interior (closure A) = interior (closure (interior A)) := by
    simpa using congrArg (fun S : Set X => interior S) hEq
  simpa [hIntEq] using hxInt