

theorem interior_closure_interior_inter_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (A : Set X))) ∩ closure (interior A) =
      interior (closure (interior A)) := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    have hcl : x ∈ closure (interior (A : Set X)) := interior_subset hx
    exact ⟨hx, hcl⟩