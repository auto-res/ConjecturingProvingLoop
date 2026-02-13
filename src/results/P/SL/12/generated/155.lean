

theorem Topology.closure_interior_closure_eq_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    closure (interior (closure (A : Set X))) = closure (interior A) := by
  -- From `P1` we know that the closures of `A` and `interior A` coincide.
  have h_cl : closure (A : Set X) = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hA
  -- Rewrite the left‐hand side using `h_cl` and invoke the idempotence lemma.
  calc
    closure (interior (closure (A : Set X))) =
        closure (interior (closure (interior A))) := by
          simpa [h_cl]
    _ = closure (interior A) := by
          simpa using
            Topology.closure_interior_closure_interior_eq (X := X) (A := A)