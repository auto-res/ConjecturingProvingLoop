

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' := hA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have hInt_subset : interior A ⊆ interior (A ∪ B) := by
          have h_sub : A ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono h_sub
        exact closure_mono hInt_subset
      exact h_subset hxA'
  | inr hxB =>
      have hxB' := hB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have hInt_subset : interior B ⊆ interior (A ∪ B) := by
          have h_sub : B ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono h_sub
        exact closure_mono hInt_subset
      exact h_subset hxB'