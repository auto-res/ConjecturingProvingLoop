

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hxA : x ∈ interior (closure (interior A)) := hA hA_mem
      have h_mono : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have hIntSubset : interior A ⊆ interior (A ∪ B) := by
          have : A ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono this
        have hClosMono : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono hIntSubset
        exact interior_mono hClosMono
      exact h_mono hxA
  | inr hB_mem =>
      have hxB : x ∈ interior (closure (interior B)) := hB hB_mem
      have h_mono : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have hIntSubset : interior B ⊆ interior (A ∪ B) := by
          have : B ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono this
        have hClosMono : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono hIntSubset
        exact interior_mono hClosMono
      exact h_mono hxB