

theorem P3_closed_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 A ↔ A = interior (closure A) := by
  -- Unfold the definition of `P3`
  dsimp [Topology.P3]
  -- For a closed set, `interior (closure A)` is contained in `A`
  have h_subset : (interior (closure A) : Set X) ⊆ A := by
    have h : (interior (closure A) : Set X) ⊆ closure A := interior_subset
    simpa [hA.closure_eq] using h
  constructor
  · -- `P3 A → A = interior (closure A)`
    intro hP3
    exact Set.Subset.antisymm hP3 h_subset
  · -- `A = interior (closure A) → P3 A`
    intro h_eq
    intro x hx
    -- Rewrite `hx : x ∈ A` using the given equality
    exact (h_eq ▸ hx)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at *
  refine
    Set.union_subset
      (Set.Subset.trans hA <|
        closure_mono <|
          interior_mono (by
            intro x hx
            exact Or.inl hx))
      (Set.Subset.trans hB <|
        closure_mono <|
          interior_mono (by
            intro x hx
            exact Or.inr hx))

theorem P3_Union_family {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (h : ∀ i, Topology.P3 (s i)) : Topology.P3 (⋃ i, s i) := by
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : (s i : Set X) ⊆ interior (closure (s i)) := h i
  have hx₁ : x ∈ interior (closure (s i)) := hPi hxi
  have h_closure_mono : (closure (s i) : Set X) ⊆ closure (⋃ j, s j) :=
    closure_mono (Set.subset_iUnion _ _)
  have h_interior_mono :
      interior (closure (s i)) ⊆ interior (closure (⋃ j, s j)) :=
    interior_mono h_closure_mono
  exact h_interior_mono hx₁

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ Topology.P1 A ∧ Topology.P3 A := by
  constructor
  · intro hP2
    exact ⟨P2_implies_P1 (A := A) hP2, P2_implies_P3 (A := A) hP2⟩
  · rintro ⟨hP1, hP3⟩
    dsimp [P2, P1, P3] at hP1 hP3 ⊢
    intro x hxA
    -- First: `x` lies in `interior (closure A)` by `P3`
    have hx_int_closureA : x ∈ interior (closure A) := hP3 hxA
    -- Second: `closure A ⊆ closure (interior A)` using `P1`
    have h_closure_subset : (closure A : Set X) ⊆ closure (interior A) :=
      closure_minimal hP1 isClosed_closure
    -- Hence the interiors satisfy the analogous inclusion
    have h_interior_mono :
        interior (closure A) ⊆ interior (closure (interior A)) :=
      interior_mono h_closure_subset
    -- Combine
    exact h_interior_mono hx_int_closureA

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  simpa [hA.closure_eq, interior_univ]