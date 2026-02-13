

theorem closure_interior_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior A)) := by
  have hP1_int : Topology.P1 (interior A) :=
    (interior_has_P1_and_P3 (X := X) (A := A)).1
  exact (P1_implies_P1_closure (X := X) (A := interior A)) hP1_int