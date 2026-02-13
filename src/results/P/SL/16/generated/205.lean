

theorem Topology.closure_unionInterior_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B : Set X) ⊆
      closure (interior (A ∪ B)) := by
  -- `interior A ∪ interior B` is contained in `interior (A ∪ B)`
  have h_subset :
      (interior A ∪ interior B : Set X) ⊆ interior (A ∪ B) :=
    Topology.interior_union_subset_interior_union (X := X) (A := A) (B := B)
  -- Taking closures preserves inclusions
  exact closure_mono h_subset