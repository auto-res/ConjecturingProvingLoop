

theorem Topology.P1_closure_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure (interior (closure (interior A)))) := by
  -- First, rewrite the set using the idempotence lemma.
  have h_eq :
      closure (interior (closure (interior A))) = closure (interior A) :=
    Topology.closure_interior_closure_interior_eq_closure_interior (X := X) (A := A)
  -- We already know that `closure (interior A)` satisfies `P1`.
  have hP1 : Topology.P1 (X := X) (closure (interior A)) :=
    Topology.P1_closure_interior (X := X) (A := A)
  -- Transport `P1` along the established equality.
  simpa [h_eq] using hP1