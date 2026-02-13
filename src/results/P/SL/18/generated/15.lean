

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hPA hPB
  -- `A` is contained in the desired set
  have hA : (A : Set X) ⊆ closure (interior (A ∪ B)) := by
    have hA₁ : (A : Set X) ⊆ closure (interior A) := hPA
    have hA₂ : interior A ⊆ interior (A ∪ B) := by
      apply interior_mono
      intro x hx
      exact Or.inl hx
    exact Set.Subset.trans hA₁ (closure_mono hA₂)
  -- `B` is contained in the desired set
  have hB : (B : Set X) ⊆ closure (interior (A ∪ B)) := by
    have hB₁ : (B : Set X) ⊆ closure (interior B) := hPB
    have hB₂ : interior B ⊆ interior (A ∪ B) := by
      apply interior_mono
      intro x hx
      exact Or.inr hx
    exact Set.Subset.trans hB₁ (closure_mono hB₂)
  -- combine the two inclusions
  intro x hx
  cases hx with
  | inl hxA => exact hA hxA
  | inr hxB => exact hB hxB