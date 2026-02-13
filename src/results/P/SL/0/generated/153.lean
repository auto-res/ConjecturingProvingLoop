

theorem P1_implies_closure_interior_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      closure (interior (A : Set X)) =
        closure (interior (closure (A : Set X))) := by
  intro hP1
  -- From `P1 A` we get `closure A = closure (interior A)`.
  have hEq1 : closure (A : Set X) = closure (interior (A : Set X)) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  -- `P1` is preserved under taking closures.
  have hP1_cl : Topology.P1 (closure (A : Set X)) :=
    (Topology.P1_implies_P1_closure (X := X) (A := A)) hP1
  -- Applying the same equivalence to `closure A`.
  have hEq2 : closure (A : Set X) =
      closure (interior (closure (A : Set X))) := by
    have h :=
      (Topology.P1_iff_closure_eq_closure_interior
          (X := X) (A := closure (A : Set X))).1 hP1_cl
    simpa [closure_closure] using h
  -- Combine the two equalities.
  have : closure (interior (A : Set X)) =
      closure (interior (closure (A : Set X))) := by
    calc
      closure (interior (A : Set X)) = closure (A : Set X) := by
        simpa using hEq1.symm
      _ = closure (interior (closure (A : Set X))) := hEq2
  simpa using this