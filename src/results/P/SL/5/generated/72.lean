

theorem interior_closure_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hA : A.Nonempty) :
    (interior (closure (A : Set X))).Nonempty := by
  -- First, `P1` together with the non-emptiness of `A` gives
  -- a non-empty interior of `A`.
  have hInt : (interior (A : Set X)).Nonempty :=
    Topology.interior_nonempty_of_P1 (X := X) (A := A) hP1 hA
  -- A non-empty interior of `A` implies a non-empty interior of its closure.
  exact
    Topology.interior_closure_nonempty_of_interior_nonempty
      (X := X) (A := A) hInt