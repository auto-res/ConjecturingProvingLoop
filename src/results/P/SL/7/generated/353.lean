

theorem Topology.closureInterior_inter_subset_closure_interInteriors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A ∩ interior B) := by
  -- Start from the basic inclusion
  -- `interior (A ∩ B) ⊆ interior A ∩ interior B`.
  have h :
      (interior (A ∩ B) : Set X) ⊆ interior A ∩ interior B :=
    Topology.interior_inter_subset_inter_interior (A := A) (B := B)
  -- Taking closures preserves inclusions, yielding the desired result.
  exact closure_mono h