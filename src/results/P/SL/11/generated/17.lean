

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hAx =>
      -- `x ∈ A`, use `hA` to send it into the desired closure
      have hxA : x ∈ closure (interior A) := hA hAx
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hsubset hxA
  | inr hBx =>
      -- `x ∈ B`, use `hB` to send it into the desired closure
      have hxB : x ∈ closure (interior B) := hB hBx
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hsubset hxB