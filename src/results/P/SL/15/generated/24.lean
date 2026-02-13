

theorem P1_closed_iff_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 A ↔ A = closure (interior A) := by
  have h_closure_eq : closure A = A := hA_closed.closure_eq
  have h₀ : Topology.P1 A ↔ closure A = closure (interior A) :=
    Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)
  simpa [h_closure_eq] using h₀