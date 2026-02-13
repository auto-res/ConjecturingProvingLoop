

theorem interior_inter_eq_empty_of_interiors_disjoint
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : interior (A : Set X) ∩ interior (B : Set X) = ∅) :
    interior ((A ∩ B) : Set X) = (∅ : Set X) := by
  -- `interior (A ∩ B)` is contained in `interior A ∩ interior B`.
  have hSub :
      (interior ((A ∩ B) : Set X) : Set X) ⊆
        interior (A : Set X) ∩ interior (B : Set X) :=
    Topology.interior_inter_subset_interiors (X := X) (A := A) (B := B)
  -- By the disjointness assumption, the right‐hand side is empty.
  have hSubEmpty :
      (interior ((A ∩ B) : Set X) : Set X) ⊆ (∅ : Set X) := by
    simpa [h] using hSub
  -- Conclude the desired equality of sets.
  exact Set.Subset.antisymm hSubEmpty (Set.empty_subset _)