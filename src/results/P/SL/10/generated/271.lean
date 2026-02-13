

theorem Topology.closure_union_interior_subset_union_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) ⊆
      closure (interior A) ∪ closure (interior B) := by
  intro x hx
  -- Use the distributivity of `closure` over unions.
  have h :
      closure (interior A ∪ interior B) =
        closure (interior A) ∪ closure (interior B) := by
    simpa using closure_union (interior A) (interior B)
  -- Rewrite `hx` via the explicit equality and finish.
  simpa [h] using hx