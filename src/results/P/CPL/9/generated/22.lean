

theorem P2_closed_iff_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 (A := A) ↔ A = interior (closure (interior A)) := by
  classical
  constructor
  · intro hP2
    -- `hP2` already gives `A ⊆ interior (closure (interior A))`.
    apply Set.Subset.antisymm hP2
    intro x hx_int
    -- From the interior we move to the closure.
    have hx_cl : (x : X) ∈ closure (interior A) := interior_subset hx_int
    -- Since `A` is closed and `interior A ⊆ A`, we have
    -- `closure (interior A) ⊆ A`.
    have h_closure_subset : closure (interior A) ⊆ A := by
      have h_sub : (interior A : Set X) ⊆ A := interior_subset
      have h_cl : closure (interior A) ⊆ closure A := closure_mono h_sub
      simpa [hA.closure_eq] using h_cl
    exact h_closure_subset hx_cl
  · intro h_eq
    -- Use the assumed equality to obtain the required inclusion.
    intro x hxA
    exact (h_eq ▸ hxA)

theorem P2_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 (A := A)) : A ⊆ interior (closure A) := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have h_sub :
      (interior (closure (interior A)) : Set X) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono interior_subset
  exact h_sub hx'

theorem P1_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P1 (A := A)) : Topology.P1 (A := Set.prod A (Set.univ : Set Y)) := by
  -- `Set.univ : Set Y` satisfies `P1`.
  have hB : Topology.P1 (A := (Set.univ : Set Y)) := by
    simpa using Topology.P1_univ (X := Y)
  -- Apply the product lemma.
  simpa using
    (Topology.P1_prod (A := A) (B := (Set.univ : Set Y)) hA hB)

theorem P2_prod_right_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : Topology.P2 (A := B)) : Topology.P2 (A := Set.prod (Set.univ : Set X) B) := by
  simpa using
    (Topology.P2_product
      (A := (Set.univ : Set X)) (B := B)
      (hA := Topology.P2_univ (X := X)) (hB := hB))

theorem exists_maximal_P2_subset {X : Type*} [TopologicalSpace X] : ∀ A : Set X, ∃ B, A ⊆ B ∧ Topology.P2 (A := B) ∧ ∀ C, B ⊆ C → Topology.P2 (A := C) → C = B := by
  intro A
  classical
  -- Define the family of `P2` supersets of `A`.
  let 𝒜 : Set (Set X) := {B | A ⊆ B ∧ Topology.P2 (A := B)}
  -- Define `B` to be the union of all sets in `𝒜`.
  let B : Set X := ⋃₀ 𝒜
  -- First, show `A ⊆ B`.
  have hAB : A ⊆ B := by
    intro x hx
    -- `Set.univ` belongs to `𝒜`.
    have h_univ_mem : (Set.univ : Set X) ∈ 𝒜 := by
      show A ⊆ (Set.univ : Set X) ∧ Topology.P2 (A := (Set.univ : Set X))
      exact ⟨Set.subset_univ _, Topology.P2_univ (X := X)⟩
    -- Hence `x` lies in the union.
    exact
      (Set.mem_sUnion.2 ⟨Set.univ, h_univ_mem, by trivial⟩ : x ∈ ⋃₀ 𝒜)
  -- Next, show that `B` satisfies `P2`.
  have hB_P2 : Topology.P2 (A := B) := by
    -- Each member of `𝒜` satisfies `P2`.
    have h_family : ∀ C ∈ 𝒜, Topology.P2 (A := C) := by
      intro C hC
      have : A ⊆ C ∧ Topology.P2 (A := C) := by
        simpa [𝒜] using hC
      exact this.2
    -- Use the `P2` lemma for unions.
    have : Topology.P2 (A := ⋃₀ 𝒜) :=
      Topology.P2_sUnion (𝒜 := 𝒜) h_family
    simpa [B] using this
  -- Finally, establish maximality of `B`.
  have h_max :
      ∀ C, B ⊆ C → Topology.P2 (A := C) → C = B := by
    intro C hBC hP2C
    -- Since `A ⊆ B ⊆ C`, we have `A ⊆ C`.
    have hAC : A ⊆ C := hAB.trans hBC
    -- Thus `C` lies in `𝒜`.
    have hC_mem : C ∈ 𝒜 := by
      show A ⊆ C ∧ Topology.P2 (A := C)
      exact ⟨hAC, hP2C⟩
    -- Every element of `C` is in `B`.
    have hCB : C ⊆ B := by
      intro x hx
      exact Set.mem_sUnion.2 ⟨C, hC_mem, hx⟩
    -- Conclude equality.
    exact Set.Subset.antisymm hCB hBC
  -- Assemble the required data.
  exact ⟨B, hAB, hB_P2, h_max⟩