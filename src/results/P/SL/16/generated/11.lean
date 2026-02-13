

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (X := X) A → Topology.P2 (X := X) B → Topology.P2 (X := X) (A ∪ B) := by
  intro hPA hPB
  dsimp [Topology.P2] at hPA hPB ⊢
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      have hxA' : x ∈ interior (closure (interior A)) := hPA hxA
      have h_subset : interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B))) := by
        have h_closure_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have h_int_subset : interior A ⊆ interior (A ∪ B) := by
            have hA_subset : A ⊆ A ∪ B := by
              intro y hy
              exact Or.inl hy
            exact interior_mono hA_subset
          exact h_int_subset
        exact interior_mono h_closure_subset
      exact h_subset hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure (interior B)) := hPB hxB
      have h_subset : interior (closure (interior B)) ⊆ interior (closure (interior (A ∪ B))) := by
        have h_closure_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have h_int_subset : interior B ⊆ interior (A ∪ B) := by
            have hB_subset : B ⊆ A ∪ B := by
              intro y hy
              exact Or.inr hy
            exact interior_mono hB_subset
          exact h_int_subset
        exact interior_mono h_closure_subset
      exact h_subset hxB'