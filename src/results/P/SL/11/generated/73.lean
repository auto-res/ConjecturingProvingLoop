

theorem P2_iff_P3_of_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : closure A = closure (interior A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  have h := Topology.P2_iff_P3_and_closure_eq_closure_interior (A := A)
  constructor
  · intro hP2
    exact (h.mp hP2).left
  · intro hP3
    exact (h.mpr ⟨hP3, hEq⟩)