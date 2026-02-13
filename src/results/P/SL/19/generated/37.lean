

theorem Topology.P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) → Topology.P3 (A := A) → Topology.P2 (A := A) := by
  intro hP1 hP3
  dsimp [Topology.P2]
  intro x hxA
  have hxIntClosA : x ∈ interior (closure A) := hP3 hxA
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  simpa [hEq] using hxIntClosA