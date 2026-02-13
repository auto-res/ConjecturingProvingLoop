

theorem Topology.closureInterior_iterate_idempotent₃
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior
      (closure (interior (closure (interior A))))))))) =
      closure (interior A) := by
  -- First, use the three–step idempotence lemma on `closure (interior A)`.
  have hStep1 :
      closure (interior (closure (interior (closure (interior
        (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closureInterior_iterate_idempotent
        (X := X) (A := closure (interior A)))
  -- Next, apply the basic idempotence lemma to `A` itself.
  have hStep2 :
      closure (interior (closure (interior A))) =
        closure (interior A) := by
    simpa using
      (Topology.closureInterior_idempotent (X := X) (A := A))
  -- Combining the two equalities yields the desired result.
  simpa using hStep1.trans hStep2