

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P1] at hA hB ⊢
  -- `A` is contained in the target set.
  have hA' : (A : Set X) ⊆ closure (interior (A ∪ B)) := by
    have hMono : closure (interior A : Set X) ⊆ closure (interior (A ∪ B)) := by
      apply closure_mono
      exact interior_mono (Set.subset_union_left)
    exact hA.trans hMono
  -- `B` is contained in the target set.
  have hB' : (B : Set X) ⊆ closure (interior (A ∪ B)) := by
    have hMono : closure (interior B : Set X) ⊆ closure (interior (A ∪ B)) := by
      apply closure_mono
      exact interior_mono (Set.subset_union_right)
    exact hB.trans hMono
  -- Combine the two inclusions.
  intro x hx
  cases hx with
  | inl hxA => exact hA' hxA
  | inr hxB => exact hB' hxB