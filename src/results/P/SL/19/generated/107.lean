

theorem Topology.P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := closure A) → Topology.P3 (A := A) := by
  intro hP2
  dsimp [Topology.P3]
  intro x hxA
  have hx_closure : x ∈ closure A := subset_closure hxA
  have hx_int : x ∈ interior (closure (interior (closure A))) := hP2 hx_closure
  have hEq :=
    Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A)
  simpa [hEq] using hx_int