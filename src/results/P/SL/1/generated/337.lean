

theorem closure_interior_closure_comp
    {X : Type*} [TopologicalSpace X] :
    ((fun A : Set X => closure (interior (closure A))) ∘
        (fun A : Set X => closure (interior (closure A)))) =
      (fun A : Set X => closure (interior (closure A))) := by
  funext A
  -- Abbreviate `F S = closure (interior (closure S))`.
  have h₁ :
      closure (interior (closure (closure (interior (closure A))))) =
        closure (interior (closure (interior (closure A)))) := by
    -- First contraction: remove the outermost redundant `closure`.
    simpa using
      (Topology.closure_interior_closure_closure_eq_closure_interior_closure
        (A := interior (closure A)))
  have h₂ :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) := by
    -- Second contraction: collapse the nested `interior`.
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior
        (A := closure A))
  -- Combine the two equalities to obtain idempotence.
  simpa [Function.comp] using (h₁.trans h₂)