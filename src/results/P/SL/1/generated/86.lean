

theorem Topology.P2_of_P3_and_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A)
    (hEq : interior (closure A) = interior (closure (interior A))) :
    Topology.P2 A := by
  dsimp [Topology.P2, Topology.P3] at hP3 ⊢
  intro x hx
  have hx_int : x ∈ interior (closure A) := hP3 hx
  simpa [hEq] using hx_int