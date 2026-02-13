

theorem Topology.P1_closure_iff_closure_eq_closureInteriorClosure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure (A : Set X)) ↔
      closure (A : Set X) = closure (interior (closure A)) := by
  -- Apply the general characterization of `P1` with `A := closure A`
  have h :
      Topology.P1 (X := X) (closure (A : Set X)) ↔
        closure (closure (A : Set X)) = closure (interior (closure (A : Set X))) :=
    Topology.P1_iff_closure_eq_closureInterior (X := X) (A := closure A)
  -- Simplify both occurrences of `closure (closure A)`
  simpa [closure_closure] using h