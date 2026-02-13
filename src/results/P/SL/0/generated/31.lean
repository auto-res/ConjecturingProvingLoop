

theorem closure_interior_closure_interior_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure (interior A)))) := by
  have hP1 : Topology.P1 (interior (closure (interior A))) :=
    (Topology.interior_closure_interior_has_all_Ps (X := X) (A := A)).1
  exact (Topology.P1_implies_P1_closure (X := X) (A := interior (closure (interior A)))) hP1