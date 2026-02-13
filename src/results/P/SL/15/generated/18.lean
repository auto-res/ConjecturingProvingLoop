

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hAx : x ∈ closure (interior A) := hA hA_mem
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have hIntSubset : interior A ⊆ interior (A ∪ B) := by
          have h_sub : A ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono h_sub
        exact closure_mono hIntSubset
      exact h_subset hAx
  | inr hB_mem =>
      have hBx : x ∈ closure (interior B) := hB hB_mem
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have hIntSubset : interior B ⊆ interior (A ∪ B) := by
          have h_sub : B ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono h_sub
        exact closure_mono hIntSubset
      exact h_subset hBx