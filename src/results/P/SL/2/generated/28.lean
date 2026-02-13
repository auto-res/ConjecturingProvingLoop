

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hP2A hP2B
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      -- `x` belongs to `A`
      have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
      -- relate the targets
      have hsubset : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        -- first on closures
        have hcl : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          -- first on interiors
          have hsub : interior A ⊆ interior (A ∪ B) := by
            have hAB : (A : Set X) ⊆ A ∪ B := by
              intro y hy
              exact Or.inl hy
            exact interior_mono hAB
          exact closure_mono hsub
        exact interior_mono hcl
      exact hsubset hx_int
  | inr hxB =>
      -- `x` belongs to `B`
      have hx_int : x ∈ interior (closure (interior B)) := hP2B hxB
      -- relate the targets
      have hsubset : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        -- first on closures
        have hcl : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          -- first on interiors
          have hsub : interior B ⊆ interior (A ∪ B) := by
            have hBB : (B : Set X) ⊆ A ∪ B := by
              intro y hy
              exact Or.inr hy
            exact interior_mono hBB
          exact closure_mono hsub
        exact interior_mono hcl
      exact hsubset hx_int