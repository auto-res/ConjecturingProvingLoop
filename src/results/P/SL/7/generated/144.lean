

theorem Topology.closureInteriorClosureInteriorClosureInterior_eq_closureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  -- First reduction using the idempotence lemma with `A := closure (interior A)`
  have h1 :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closureInteriorClosureInterior_eq_closureInterior
        (A := closure (interior A)))
  -- Second reduction using the idempotence lemma with the original set `A`
  have h2 :
      closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using
      (Topology.closureInteriorClosureInterior_eq_closureInterior
        (A := A))
  simpa [h1, h2]