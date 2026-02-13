

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_in : x ∈ interior (closure (interior A)) := hA hxA
      have hMono : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have hIntSub : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        have hClSub : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono hIntSub
        exact interior_mono hClSub
      exact hMono hx_in
  | inr hxB =>
      have hx_in : x ∈ interior (closure (interior B)) := hB hxB
      have hMono : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have hIntSub : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        have hClSub : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono hIntSub
        exact interior_mono hClSub
      exact hMono hx_in