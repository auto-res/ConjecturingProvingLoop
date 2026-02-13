

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at hA hB ⊢
  -- `A` is contained in `interior (closure (A ∪ B))`
  have hA' : (A : Set X) ⊆ interior (closure (A ∪ B)) := by
    have hA_to_int : (A : Set X) ⊆ interior (closure A) := hA
    have h_int_mono : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
      have h_closure_mono : closure A ⊆ closure (A ∪ B) := by
        have h_subset : (A : Set X) ⊆ (A ∪ B) := by
          intro x hx
          exact Or.inl hx
        exact closure_mono h_subset
      exact interior_mono h_closure_mono
    exact Set.Subset.trans hA_to_int h_int_mono
  -- `B` is contained in `interior (closure (A ∪ B))`
  have hB' : (B : Set X) ⊆ interior (closure (A ∪ B)) := by
    have hB_to_int : (B : Set X) ⊆ interior (closure B) := hB
    have h_int_mono : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
      have h_closure_mono : closure B ⊆ closure (A ∪ B) := by
        have h_subset : (B : Set X) ⊆ (A ∪ B) := by
          intro x hx
          exact Or.inr hx
        exact closure_mono h_subset
      exact interior_mono h_closure_mono
    exact Set.Subset.trans hB_to_int h_int_mono
  -- Hence `A ∪ B` is contained in `interior (closure (A ∪ B))`
  exact Set.union_subset hA' hB'