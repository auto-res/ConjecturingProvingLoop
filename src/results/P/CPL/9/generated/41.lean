

theorem P1_bigUnion₂ {X : Type*} [TopologicalSpace X] {ι κ} (s : ι → κ → Set X) (h : ∀ i j, Topology.P1 (A := s i j)) : Topology.P1 (A := ⋃ i, ⋃ j, s i j) := by
  -- First, for each fixed `i`, the union over `j` satisfies `P1`.
  have h₁ : ∀ i, Topology.P1 (A := ⋃ j, s i j) := by
    intro i
    have : Topology.P1 (A := ⋃ j, s i j) :=
      Topology.P1_Union (s := s i) (h := fun j => h i j)
    simpa using this
  -- Then take the union over `i`.
  have h₂ : Topology.P1 (A := ⋃ i, ⋃ j, s i j) :=
    Topology.P1_Union (s := fun i => ⋃ j, s i j) (h := h₁)
  simpa using h₂