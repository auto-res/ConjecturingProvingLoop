

theorem Topology.dense_closure_iff_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (closure (A : Set X)) ↔ Dense (A : Set X) := by
  -- Rewrite both `Dense` predicates in terms of closures being the whole space.
  have h₁ :
      Dense (closure (A : Set X)) ↔
        closure (closure (A : Set X)) = (Set.univ : Set X) :=
    (dense_iff_closure_eq (s := (closure (A : Set X))))
  have h₂ :
      Dense (A : Set X) ↔
        closure (A : Set X) = (Set.univ : Set X) :=
    (dense_iff_closure_eq (s := (A : Set X)))
  -- Since `closure (closure A)` coincides with `closure A`, these conditions are equivalent.
  have h_eq :
      (closure (closure (A : Set X)) = (Set.univ : Set X)) ↔
        closure (A : Set X) = (Set.univ : Set X) := by
    simpa [closure_closure]
  -- Chain the equivalences to obtain the desired result.
  simpa using h₁.trans (h_eq.trans h₂.symm)