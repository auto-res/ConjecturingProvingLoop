

theorem Topology.P1_implies_interior_closure_eq_interior_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X:=X) A →
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
  intro hP1
  have h_cl : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (X:=X) (A:=A)).1 hP1
  simpa [h_cl]