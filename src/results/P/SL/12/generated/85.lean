

theorem Topology.interior_closure_eq_interior_closure_interior_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P3 (X := X) A) :
    interior (closure (A : Set X)) =
      interior (closure (interior (closure A))) := by
  -- `P3` for `A` gives `P1` for `closure A`.
  have hP1 : Topology.P1 (X := X) (closure A) :=
    Topology.P3_implies_P1_closure (X := X) (A := A) hA
  -- Apply the existing equality for `P1`.
  have h_eq :
      interior (closure (closure (A : Set X))) =
        interior (closure (interior (closure A))) :=
    Topology.interior_closure_eq_interior_closure_interior_of_P1
      (X := X) (A := closure A) hP1
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using h_eq