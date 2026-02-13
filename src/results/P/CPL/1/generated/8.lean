

theorem P2_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ interior A = A := by
  refine ⟨?forward, ?backward⟩
  · intro hP2
    exact interior_eq_of_P2_closed (A := A) hA hP2
  · intro h_int_eq
    intro x hx
    simpa [h_int_eq, hA.closure_eq] using hx