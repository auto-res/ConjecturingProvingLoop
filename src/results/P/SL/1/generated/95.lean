

theorem Topology.P1_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → B ⊆ closure (interior A) → Topology.P1 (A ∪ B) := by
  intros hA hB
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      -- The point comes from `A`; use `P1` for `A`.
      have hx_closure : x ∈ closure (interior A) := hA hxA
      -- Upgrade the membership via monotonicity of `interior` and `closure`.
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact hsubset hx_closure
  | inr hxB =>
      -- The point comes from `B`; use the subset assumption.
      have hx_closure : x ∈ closure (interior A) := hB hxB
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact hsubset hx_closure