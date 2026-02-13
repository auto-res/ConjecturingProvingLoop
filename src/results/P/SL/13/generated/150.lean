

theorem Topology.P1_closureInteriorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure (interior (closure (A : Set X)))) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior (closure (interior (closure A)))` simplifies to `interior (closure A)`
  -- via an existing lemma; hence their closures coincide.
  have h_int_eq :
      interior (closure (interior (closure (A : Set X)))) =
        interior (closure (A : Set X)) := by
    simpa using
      (Topology.interior_closure_interior_closure_eq_interior_closure
        (X := X) (A := A))
  -- Rewrite the target set using `h_int_eq` and conclude with `hx`.
  simpa [h_int_eq] using hx