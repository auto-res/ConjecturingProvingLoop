

theorem closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure (A : Set X) = closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 A := (Topology.P2_implies_P1 (X := X) (A := A)) hP2
  exact (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1