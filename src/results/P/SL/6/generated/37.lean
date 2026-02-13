

theorem P3_union_of_P3 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 (A : Set X)) (hB : Topology.P3 (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ interior (closure A) := hA hAx
      have hIncl : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure (A : Set X) ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact hIncl hxA
  | inr hBx =>
      have hxB : x ∈ interior (closure B) := hB hBx
      have hIncl : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure (B : Set X) ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact hIncl hxB