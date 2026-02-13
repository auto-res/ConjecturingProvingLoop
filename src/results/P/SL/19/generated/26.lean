

theorem Topology.P2_iff_P3_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) → (Topology.P2 (A := A) ↔ Topology.P3 (A := A)) := by
  intro hP1
  have hEq :=
    (Topology.interior_closure_eq_interior_closure_interior_of_P1 (A := A) hP1).symm
  simpa [Topology.P2, Topology.P3, hEq]