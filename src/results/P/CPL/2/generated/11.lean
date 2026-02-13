

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (hA : ∀ A ∈ 𝒜, Topology.P2 (X:=X) A) : Topology.P2 (X:=X) (⋃₀ 𝒜) := by
  classical
  -- Unpack the definition of `P2`
  unfold Topology.P2 at hA ⊢
  intro x hx
  -- Obtain a witness set `A`
  rcases hx with ⟨A, hA_mem, hxA⟩
  -- Apply `P2` for this particular `A`
  have hx₁ : x ∈ interior (closure (interior A)) := (hA A hA_mem) hxA
  -- Show the required inclusion of interiors
  have h_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    -- Use monotonicity of `interior` and `closure`
    apply interior_mono
    have h_closure_subset :
        closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
      apply closure_mono
      have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
        apply interior_mono
        intro y hy
        exact ⟨A, hA_mem, hy⟩
      exact h_int_subset
    exact h_closure_subset
  -- Conclude
  exact h_subset hx₁

theorem dense_of_P1_and_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 (X:=X) A) (h_dense : Dense (interior A)) : Dense A := by
  -- Step 1: show `closure A ⊆ closure (interior A)`
  have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
    -- `P1` gives `A ⊆ closure (interior A)`
    -- Taking closures and simplifying yields the claim
    have : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono h
    simpa [closure_closure] using this
  -- Step 2: the reverse inclusion `closure (interior A) ⊆ closure A`
  have h₂ : closure (interior A) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Step 3: deduce equality of the two closures
  have h_closure_eq : closure (A : Set X) = closure (interior A) :=
    (subset_antisymm h₁ h₂)
  -- Step 4: use density of `interior A`
  have h_closure_univ : closure (A : Set X) = (Set.univ : Set X) := by
    simpa [h_closure_eq] using h_dense.closure_eq
  -- Step 5: conclude that `A` is dense
  exact (dense_iff_closure_eq).mpr h_closure_univ

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen (closure A)) : Topology.P3 (X:=X) A := by
  unfold Topology.P3
  -- Since `closure A` is open, its interior is itself
  have h_eq : interior (closure (A : Set X)) = closure A := by
    simpa using h_open.interior_eq
  -- The set `A` is contained in its closure
  have h_sub : (A : Set X) ⊆ closure A := subset_closure
  -- Combine the two facts
  simpa [h_eq] using h_sub

theorem P2_bUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {s : Set ι} {A : ι → Set X} (hA : ∀ i, i ∈ s → Topology.P2 (X:=X) (A i)) : Topology.P2 (X:=X) (⋃ i, ⋃ (_h : i ∈ s), A i) := by
  classical
  -- Step 1: obtain `P2` for every index contained in `s`
  have h_subtype : ∀ z : {i // i ∈ s}, Topology.P2 (X := X) (A z.1) := by
    intro z
    exact hA z.1 z.2
  -- Step 2: apply `P2_Union` to this family
  have hP2_sub :
      Topology.P2 (X := X) (⋃ z : {i // i ∈ s}, A z.1) := by
    simpa using
      (Topology.P2_Union (X := X) (A := fun z : {i // i ∈ s} => A z.1)
        (by
          intro z
          exact h_subtype z))
  -- Step 3: identify the two unions
  have h_eq :
      (⋃ z : {i // i ∈ s}, A z.1) = ⋃ i, ⋃ _h : i ∈ s, A i := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨z, hxz⟩
      rcases z with ⟨i, hi⟩
      exact
        (Set.mem_iUnion.2
            ⟨i, Set.mem_iUnion.2 ⟨hi, by simpa using hxz⟩⟩)
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx₁⟩
      rcases Set.mem_iUnion.1 hx₁ with ⟨hi, hxi⟩
      exact
        (Set.mem_iUnion.2
            ⟨⟨i, hi⟩, by simpa using hxi⟩)
  -- Step 4: rewrite and conclude
  simpa [h_eq] using hP2_sub