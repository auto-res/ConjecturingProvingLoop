

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 (A : Set X)) (hB : Topology.P3 (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at *
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : (x : X) ∈ interior (closure A) := hA hAx
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure (A : Set X) ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact h_subset hxA
  | inr hBx =>
      have hxB : (x : X) ∈ interior (closure B) := hB hBx
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure (B : Set X) ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact h_subset hxB