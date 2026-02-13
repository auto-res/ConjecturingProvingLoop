

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (X := X) A → Topology.P3 (X := X) B → Topology.P3 (X := X) (A ∪ B) := by
  intro hPA hPB
  dsimp [Topology.P3] at hPA hPB ⊢
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      have hxA' : x ∈ interior (closure A) := hPA hxA
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have h_closure_subset : closure A ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact interior_mono h_closure_subset
      exact h_subset hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure B) := hPB hxB
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have h_closure_subset : closure B ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact interior_mono h_closure_subset
      exact h_subset hxB'