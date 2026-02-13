

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hP3A hP3B
  -- Unfold the definition of `P3`.
  dsimp [Topology.P3] at hP3A hP3B ⊢
  -- Goal: `A ∪ B ⊆ interior (closure (A ∪ B))`.
  intro x hx
  cases hx with
  | inl hxA =>
      -- From `P3` for `A`, we know `x ∈ interior (closure A)`.
      have hxA' : x ∈ interior (closure A) := hP3A hxA
      -- This interior is contained in the required interior.
      have hIncl : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        -- First, show `closure A ⊆ closure (A ∪ B)`.
        have hSub : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact closure_mono hSub
      exact hIncl hxA'
  | inr hxB =>
      -- From `P3` for `B`, we know `x ∈ interior (closure B)`.
      have hxB' : x ∈ interior (closure B) := hP3B hxB
      -- This interior is contained in the required interior.
      have hIncl : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        -- First, show `closure B ⊆ closure (A ∪ B)`.
        have hSub : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact closure_mono hSub
      exact hIncl hxB'