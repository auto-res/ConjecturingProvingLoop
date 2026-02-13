

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intros hA hB
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_closure : x ∈ closure (interior A) := hA hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior A ⊆ interior (A ∪ B) := by
          have hAB : A ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono hAB
        exact this
      exact hsubset hx_closure
  | inr hxB =>
      have hx_closure : x ∈ closure (interior B) := hB hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior B ⊆ interior (A ∪ B) := by
          have hBA : B ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono hBA
        exact this
      exact hsubset hx_closure