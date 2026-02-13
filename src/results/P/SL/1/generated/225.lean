

theorem Topology.closure_interior_inter_subset_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A ∩ interior B) := by
  -- Start with the inclusion between the interiors.
  have hsubset : interior (A ∩ B) ⊆ interior A ∩ interior B :=
    Topology.interior_inter_subset (A := A) (B := B)
  -- Taking closures preserves inclusions.
  exact closure_mono hsubset