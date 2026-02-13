

theorem interior_closure_interior_inter_subset_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior ((A ∩ B) : Set X))) ⊆
      interior (closure (interior (A : Set X))) ∩
        interior (closure (interior (B : Set X))) := by
  -- First, relate the closures of the interiors.
  have h₁ :
      closure (interior ((A ∩ B) : Set X)) ⊆
        closure (interior (A : Set X)) ∩ closure (interior (B : Set X)) :=
    Topology.closure_interior_inter_subset_intersection
      (X := X) (A := A) (B := B)
  -- Apply `interior_mono` to obtain an inclusion between the interiors.
  have h₂ :
      interior (closure (interior ((A ∩ B) : Set X))) ⊆
        interior
          (closure (interior (A : Set X)) ∩ closure (interior (B : Set X))) :=
    interior_mono h₁
  -- Distribute `interior` over the intersection on the right‐hand side.
  have h₃ :
      interior
          (closure (interior (A : Set X)) ∩ closure (interior (B : Set X))) ⊆
        interior (closure (interior (A : Set X))) ∩
          interior (closure (interior (B : Set X))) := by
    simpa using
      (Topology.interior_inter_subset_interiors
        (X := X)
        (A := closure (interior (A : Set X)))
        (B := closure (interior (B : Set X))))
  exact h₂.trans h₃