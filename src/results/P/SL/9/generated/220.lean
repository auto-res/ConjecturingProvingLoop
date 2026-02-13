

theorem Topology.boundary_eq_empty_iff_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (A : Set X) \ interior A = (∅ : Set X)) ↔ (IsClosed A ∧ IsOpen A) := by
  constructor
  · intro h
    exact Topology.isClopen_of_boundary_eq_empty (A := A) h
  · rintro ⟨hClosed, hOpen⟩
    exact Topology.boundary_eq_empty_of_isClopen (A := A) hClosed hOpen