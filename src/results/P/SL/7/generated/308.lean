

theorem Topology.closureInterior_iter3_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  -- Apply the basic two-step idempotence lemma with `A := interior A`.
  have h :=
    Topology.closureInteriorClosureInterior_eq_closureInterior
      (A := interior A)
  -- Simplify the right-hand side using `interior_interior`.
  simpa [interior_interior] using h