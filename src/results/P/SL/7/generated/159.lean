

theorem Topology.interiorClosure_iter4_idempotent {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior
      (closure (interior (closure A))))))))) =
      interior (closure A) := by
  -- First, use the `iter3` idempotence lemma to simplify the innermost part.
  have h₁ :=
    Topology.interiorClosure_iter3_idempotent (A := A)
  have h₂ :
      interior (closure (interior (closure (interior (closure (interior
        (closure (interior (closure A))))))))) =
        interior (closure (interior (closure A))) := by
    simpa [h₁]
  -- A final application of the basic idempotence lemma finishes the proof.
  calc
    interior (closure (interior (closure (interior (closure (interior
      (closure (interior (closure A))))))))) =
        interior (closure (interior (closure A))) := h₂
    _ = interior (closure A) :=
        Topology.interiorClosure_idempotent (A := A)