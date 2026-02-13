

theorem Topology.interior_closure_iterate_five_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  -- First, collapse the innermost three iterations using the idempotence lemma.
  have h₁ :=
    Topology.interior_closure_interior_closure_eq
      (X := X) (A := interior (closure A))
  -- Next, collapse the remaining two iterations in exactly the same way.
  have h₂ :=
    Topology.interior_closure_interior_closure_eq
      (X := X) (A := A)
  -- Chain the two equalities to obtain the desired result.
  simpa using h₁.trans h₂