

theorem P1_union_of_P1 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (A : Set X)) (hB : Topology.P1 (B : Set X)) :
    Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ closure (interior A) := hA hAx
      have hIncl : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hIncl hxA
  | inr hBx =>
      have hxB : x ∈ closure (interior B) := hB hBx
      have hIncl : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hIncl hxB