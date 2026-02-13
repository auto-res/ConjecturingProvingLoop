

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (A : Set X)) (hB : Topology.P2 (B : Set X)) :
    Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at *
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : (x : X) ∈ interior (closure (interior A)) := hA hAx
      have h_subset : interior (closure (interior A))
          ⊆ interior (closure (interior (A ∪ B))) := by
        have h_closure : closure (interior A)
            ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have h_int : interior A ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inl hy
          exact h_int
        exact interior_mono h_closure
      exact h_subset hxA
  | inr hBx =>
      have hxB : (x : X) ∈ interior (closure (interior B)) := hB hBx
      have h_subset : interior (closure (interior B))
          ⊆ interior (closure (interior (A ∪ B))) := by
        have h_closure : closure (interior B)
            ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have h_int : interior B ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inr hy
          exact h_int
        exact interior_mono h_closure
      exact h_subset hxB