

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at *
  refine Set.union_subset ?_ ?_
  ·
    have hMono : interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B))) := by
      have h1 : (interior A : Set X) ⊆ interior (A ∪ B) := by
        have hA_subset : (A : Set X) ⊆ A ∪ B := by
          intro x hx
          exact Or.inl hx
        exact interior_mono hA_subset
      have h2 : (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h1
      exact interior_mono h2
    exact Set.Subset.trans hA hMono
  ·
    have hMono : interior (closure (interior B)) ⊆ interior (closure (interior (A ∪ B))) := by
      have h1 : (interior B : Set X) ⊆ interior (A ∪ B) := by
        have hB_subset : (B : Set X) ⊆ A ∪ B := by
          intro x hx
          exact Or.inr hx
        exact interior_mono hB_subset
      have h2 : (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h1
      exact interior_mono h2
    exact Set.Subset.trans hB hMono

theorem P1_Union_family {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (h : ∀ i, Topology.P1 (s i)) : Topology.P1 (⋃ i, s i) := by
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : (s i : Set X) ⊆ closure (interior (s i)) := h i
  have hx_closure : x ∈ closure (interior (s i)) := hPi hxi
  have h_int_mono : interior (s i) ⊆ interior (⋃ j, s j) :=
    interior_mono (Set.subset_iUnion _ _)
  have h_closure_mono :
      closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) :=
    closure_mono h_int_mono
  exact h_closure_mono hx_closure