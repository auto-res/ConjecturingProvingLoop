

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxInt : x ∈ interior (closure (interior A)) := hA hxA
      have hsubset : interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B))) := by
        have h₁ : interior A ⊆ interior (A ∪ B) := by
          have : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono this
        have h₂ : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        exact interior_mono h₂
      exact hsubset hxInt
  | inr hxB =>
      have hxInt : x ∈ interior (closure (interior B)) := hB hxB
      have hsubset : interior (closure (interior B)) ⊆ interior (closure (interior (A ∪ B))) := by
        have h₁ : interior B ⊆ interior (A ∪ B) := by
          have : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono this
        have h₂ : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        exact interior_mono h₂
      exact hsubset hxInt