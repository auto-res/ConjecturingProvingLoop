

theorem P2_union_of_P2 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (A : Set X)) (hB : Topology.P2 (B : Set X)) :
    Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ interior (closure (interior A)) := hA hAx
      have hIncl : interior (closure (interior A))
          ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        have : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact hIncl hxA
  | inr hBx =>
      have hxB : x ∈ interior (closure (interior B)) := hB hBx
      have hIncl : interior (closure (interior B))
          ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        have : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact hIncl hxB