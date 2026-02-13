

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hP1A hP1B
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      have hx_closure : x ∈ closure (interior A) := hP1A hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have h₁ : interior A ⊆ interior (A ∪ B) := by
          have hAUB : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono hAUB
        exact closure_mono h₁
      exact hsubset hx_closure
  | inr hxB =>
      have hx_closure : x ∈ closure (interior B) := hP1B hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have h₁ : interior B ⊆ interior (A ∪ B) := by
          have hAUB : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono hAUB
        exact closure_mono h₁
      exact hsubset hx_closure