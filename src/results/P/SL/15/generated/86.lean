

theorem P3_and_P1_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 A → Topology.P2 A := by
  intro hP3 hP1
  dsimp [Topology.P2]
  intro x hx
  have hx_int_clA : x ∈ interior (closure A) := hP3 hx
  have h_cl_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  simpa [h_cl_eq] using hx_int_clA