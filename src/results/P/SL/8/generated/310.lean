

theorem P3_imp_interior_closureInteriorClosure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  have h :=
    Topology.P3_imp_closureInteriorClosure_eq_closure (X := X) (A := A) hP3
  simpa [h]