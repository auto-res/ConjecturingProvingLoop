

theorem P2_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P2 (A := A)) : Topology.P2 (A := Set.prod A (Set.univ : Set Y)) := by
  simpa using
    (Topology.P2_product
      (X := X) (Y := Y)
      (A := A) (B := (Set.univ : Set Y))
      hA
      (Topology.P2_univ (X := Y)))

theorem exists_maximal_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ Topology.P1 (A := B) ∧ ∀ C, B ⊆ C → Topology.P1 (A := C) → C = B := by
  classical
  -- Define the family of `P1` supersets of `A`.
  let 𝒜 : Set (Set X) := {B | A ⊆ B ∧ Topology.P1 (A := B)}
  -- Define `B` to be the union of all sets in `𝒜`.
  let B : Set X := ⋃₀ 𝒜
  -- First, show `A ⊆ B`.
  have hAB : A ⊆ B := by
    intro x hx
    -- `Set.univ` belongs to `𝒜`.
    have h_univ_mem : (Set.univ : Set X) ∈ 𝒜 := by
      change
        A ⊆ (Set.univ : Set X) ∧ Topology.P1 (A := (Set.univ : Set X))
      exact ⟨Set.subset_univ _, Topology.P1_univ (X := X)⟩
    -- Hence `x` lies in the union.
    have hx' : x ∈ ⋃₀ 𝒜 :=
      Set.mem_sUnion.2 ⟨(Set.univ : Set X), h_univ_mem, trivial⟩
    simpa [B] using hx'
  -- Next, show that `B` satisfies `P1`.
  have hB_P1 : Topology.P1 (A := B) := by
    -- Each member of `𝒜` satisfies `P1`.
    have h_family : ∀ C, C ∈ 𝒜 → Topology.P1 (A := C) := by
      intro C hC
      have : A ⊆ C ∧ Topology.P1 (A := C) := by
        simpa [𝒜] using hC
      exact this.2
    -- Use the `P1` lemma for unions.
    have : Topology.P1 (A := ⋃₀ 𝒜) :=
      Topology.P1_sUnion (𝒜 := 𝒜) h_family
    simpa [B] using this
  -- Finally, establish maximality of `B`.
  have h_max :
      ∀ C, B ⊆ C → Topology.P1 (A := C) → C = B := by
    intro C hBC hP1C
    -- Since `A ⊆ B ⊆ C`, we have `A ⊆ C`.
    have hAC : A ⊆ C := hAB.trans hBC
    -- Thus `C` lies in `𝒜`.
    have hC_mem : C ∈ 𝒜 := by
      change A ⊆ C ∧ Topology.P1 (A := C)
      exact ⟨hAC, hP1C⟩
    -- Every element of `C` is in `B`.
    have hCB : C ⊆ B := by
      intro x hx
      have hx' : x ∈ ⋃₀ 𝒜 :=
        Set.mem_sUnion.2 ⟨C, hC_mem, hx⟩
      simpa [B] using hx'
    -- Conclude equality.
    exact Set.Subset.antisymm hCB hBC
  -- Assemble the required data.
  exact ⟨B, hAB, hB_P1, h_max⟩