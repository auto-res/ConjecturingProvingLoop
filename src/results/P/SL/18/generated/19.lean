

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hP2A hP2B
  dsimp [Topology.P2] at hP2A hP2B ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure (interior A)) := hP2A hxA
      have hIncl : interior (closure (interior A))
          ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        have : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have : interior A ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inl hy
          exact this
        exact this
      exact hIncl hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure (interior B)) := hP2B hxB
      have hIncl : interior (closure (interior B))
          ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        have : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have : interior B ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inr hy
          exact this
        exact this
      exact hIncl hxB'