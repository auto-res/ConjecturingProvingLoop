

theorem Topology.interior_closure_interior_closure_eq_of_P1 {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : Topology.P1 (X := X) A) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  -- First, upgrade `P1` from `A` to `closure A`.
  have h_closure : Topology.P1 (X := X) (closure A) :=
    Topology.P1_closure_of_P1 (X := X) (A := A) hA
  -- Apply the existing equality for sets satisfying `P1`.
  have h_eq :
      interior (closure (closure (A : Set X))) =
        interior (closure (interior (closure A))) :=
    Topology.interior_closure_eq_interior_closure_interior_of_P1
      (X := X) (A := closure A) h_closure
  -- Simplify the left‐hand side and reorient the equality.
  simpa [closure_closure] using h_eq.symm