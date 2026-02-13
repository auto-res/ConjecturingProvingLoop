

theorem P2_iff_P3_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ Topology.P3 (closure (interior A)) := by
  have h₁ : Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) :=
    (Topology.P2_closure_interior_iff_open (A := A))
  have h₂ : Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) :=
    (Topology.P3_closure_interior_iff_open (A := A))
  simpa using h₁.trans h₂.symm