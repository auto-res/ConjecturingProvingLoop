

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (X := X) A → Topology.P1 (X := X) B → Topology.P1 (X := X) (A ∪ B) := by
  intro hPA hPB
  dsimp [Topology.P1] at hPA hPB ⊢
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      have hx_closure_intA : x ∈ closure (interior A) := hPA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have h_interior_subset : interior A ⊆ interior (A ∪ B) := by
          -- `interior` is monotone, so it respects subset relations
          have hA_subset : A ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono hA_subset
        exact h_interior_subset
      exact h_subset hx_closure_intA
  | inr hxB =>
      have hx_closure_intB : x ∈ closure (interior B) := hPB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have h_interior_subset : interior B ⊆ interior (A ∪ B) := by
          have hB_subset : B ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono hB_subset
        exact h_interior_subset
      exact h_subset hx_closure_intB