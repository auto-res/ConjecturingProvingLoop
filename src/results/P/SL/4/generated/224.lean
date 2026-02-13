

theorem P1_iff_P1_closure_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P1 A ↔ Topology.P1 (closure A) := by
  have h_cl : closure A = A := hA.closure_eq
  constructor
  · intro hP1
    exact P1_imp_P1_closure (A := A) hP1
  · intro hP1_cl
    simpa [h_cl] using hP1_cl