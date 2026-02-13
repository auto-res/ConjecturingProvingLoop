

theorem P2_sUnion_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (⋃₀ (∅ : Set (Set X))) := by
  simpa [Set.sUnion_empty] using (Topology.P2_empty (X := X))