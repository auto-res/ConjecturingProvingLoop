

theorem Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  -- First contraction using idempotence of `interior ∘ closure`.
  have h₁ :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
    simpa using
      (Topology.interior_closure_interior_closure_eq_interior_closure
        (A := interior (closure A)))
  -- Second contraction to reach the final form.
  have h₂ :
      interior (closure (interior (closure A))) = interior (closure A) := by
    simpa using
      (Topology.interior_closure_interior_closure_eq_interior_closure (A := A))
  simpa [h₁, h₂]