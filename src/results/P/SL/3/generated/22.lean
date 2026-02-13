

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (A : Set X)) (hB : Topology.P1 (B : Set X)) :
    Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : (x : X) ∈ closure (interior A) := hA hAx
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact h_subset hxA
  | inr hBx =>
      have hxB : (x : X) ∈ closure (interior B) := hB hBx
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact h_subset hxB