

theorem Topology.closure_interior_eq_self_iff_closed_and_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = A ↔ (IsClosed A ∧ Topology.P1 A) := by
  constructor
  · intro h_eq
    have h_closed : IsClosed A := by
      have : IsClosed (closure (interior A)) := isClosed_closure
      simpa [h_eq] using this
    have h_P1 : Topology.P1 A := by
      intro x hx
      simpa [h_eq] using hx
    exact And.intro h_closed h_P1
  · rintro ⟨h_closed, h_P1⟩
    exact
      Topology.closure_interior_eq_of_closed_of_P1 (A := A) h_closed h_P1