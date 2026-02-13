

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hP3A hP3B
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      -- `x` belongs to `A`
      have hx_int : x ∈ interior (closure A) := hP3A hxA
      -- `closure A` is contained in `closure (A ∪ B)`
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have hcl : closure A ⊆ closure (A ∪ B) := by
          have hAUB : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact closure_mono hAUB
        exact interior_mono hcl
      exact hsubset hx_int
  | inr hxB =>
      -- `x` belongs to `B`
      have hx_int : x ∈ interior (closure B) := hP3B hxB
      -- `closure B` is contained in `closure (A ∪ B)`
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have hcl : closure B ⊆ closure (A ∪ B) := by
          have hBUB : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact closure_mono hBUB
        exact interior_mono hcl
      exact hsubset hx_int