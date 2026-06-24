

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P1] at *
  exact fun x hx =>
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) (hP2 hx)

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at *
  intro x hx
  have hclsub : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hclsub
  exact hsubset (hP2 hx)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ closure (interior A) := hA hAx
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact hsubset hxA
  | inr hBx =>
      have hxB : x ∈ closure (interior B) := hB hBx
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact hsubset hxB

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A, A ∈ 𝒜 → Topology.P3 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro h
  dsimp [Topology.P3] at h ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA𝒜, hxA⟩
  have hP3A : Topology.P3 A := h A hA𝒜
  have hx_in_int_cl_A : x ∈ interior (closure A) := hP3A hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    apply interior_mono
    have : closure A ⊆ closure (⋃₀ 𝒜) := by
      apply closure_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA𝒜, hy⟩
    exact this
  exact hsubset hx_in_int_cl_A

theorem P1_empty {X : Type*} [TopologicalSpace X] : Topology.P1 (∅ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  cases hx