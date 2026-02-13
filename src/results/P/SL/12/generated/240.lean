

theorem Topology.P2_and_empty_interior_iff_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (Topology.P2 (X := X) A ∧ interior (A : Set X) = ∅) ↔ A = ∅ := by
  constructor
  · rintro ⟨hP2, hInt⟩
    -- From `P2`, we have the inclusion `A ⊆ interior (closure (interior A))`.
    have h_subset : (A : Set X) ⊆ interior (closure (interior A)) := hP2
    -- Since `interior A = ∅`, the right‐hand side is `∅`.
    have h_eq : interior (closure (interior A)) = (∅ : Set X) := by
      simpa [hInt, closure_empty, interior_empty]
    -- Hence `A ⊆ ∅`, so `A = ∅`.
    have h_empty : (A : Set X) ⊆ (∅ : Set X) := by
      simpa [h_eq] using h_subset
    exact Set.Subset.antisymm h_empty (Set.empty_subset _)
  · intro hA
    -- If `A = ∅`, both required conditions are immediate.
    have hP2 : Topology.P2 (X := X) A := by
      simpa [hA] using Topology.P2_empty (X := X)
    have hInt : interior (A : Set X) = (∅ : Set X) := by
      simpa [hA] using (interior_empty : interior (∅ : Set X) = ∅)
    exact And.intro hP2 hInt