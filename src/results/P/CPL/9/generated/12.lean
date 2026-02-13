

theorem P1_iff_P3_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X} (hA_open : IsOpen A) (hA_closed : IsClosed A) : Topology.P1 (A := A) ↔ Topology.P3 (A := A) := by
  have h_int : interior A = A := hA_open.interior_eq
  have h_cl : closure A = A := hA_closed.closure_eq
  constructor
  · intro _hP1
    intro x hx
    simpa [h_int, h_cl] using hx
  · intro _hP3
    intro x hx
    simpa [h_int, h_cl] using hx