

theorem P2_discrete {X} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} : P2 A := by
  have hAopen : IsOpen (A : Set X) := by
    simpa using isOpen_discrete (s := (A : Set X))
  exact P2_of_open (A := A) hAopen

theorem P2_subset_closure {X} [TopologicalSpace X] {A : Set X} : P2 A → (A : Set X) ⊆ closure (interior A) := by
  intro hP2 x hxA
  exact interior_subset (hP2 hxA)

theorem P3_nhds_basis {X} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x ∈ A, ∀ V ∈ 𝓝 x, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ U ⊆ closure A := by
  classical
  -- We use the already–proved characterisation of `P3` via open neighbourhoods.
  have h_open : P3 A ↔
      ∀ x, x ∈ A → ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A :=
    P3_iff_forall_point (A := A)
  --------------------------------------------------------------------------
  -- We now establish the required equivalence.
  --------------------------------------------------------------------------
  constructor
  · -- `P3 A →` neighbourhood‐basis statement.
    intro hP3
    -- Reformulate `hP3` in terms of open neighbourhoods.
    have hP3_open := (h_open).1 hP3
    -- Fix a point `x ∈ A` and a neighbourhood `V` of `x`.
    intro x hxA V hV
    -- Obtain an open set `U₁ ⊆ closure A` containing `x`.
    rcases hP3_open x hxA with ⟨U₁, hU₁open, hxU₁, hU₁sub⟩
    -- From `V ∈ 𝓝 x`, pick an open set `V₀` with `x ∈ V₀ ⊆ V`.
    rcases mem_nhds_iff.1 hV with ⟨V₀, hV₀sub, hV₀open, hxV₀⟩
    -- Intersect the two open sets.
    refine ⟨U₁ ∩ V₀, hU₁open.inter hV₀open, ⟨hxU₁, hxV₀⟩, ?_, ?_⟩
    · -- `U₁ ∩ V₀ ⊆ V`
      intro y hy
      exact hV₀sub hy.2
    · -- `U₁ ∩ V₀ ⊆ closure A`
      intro y hy
      exact hU₁sub hy.1
  · -- Converse: neighbourhood‐basis statement → `P3 A`.
    intro hBasis
    -- Build the open‐neighbourhood formulation required by `h_open`.
    have h_open_form :
        ∀ x, x ∈ A → ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A := by
      intro x hxA
      -- Apply the basis property with the trivial neighbourhood `univ`.
      rcases hBasis x hxA Set.univ Filter.univ_mem with
        ⟨U, hUopen, hxU, _hUsubUniv, hUsub_closure⟩
      exact ⟨U, hUopen, hxU, hUsub_closure⟩
    -- Translate back to `P3 A`.
    exact (h_open).2 h_open_form

theorem P2_sImage {X} [TopologicalSpace X] {ℱ : Set (Set X)} (h : ∀ A ∈ ℱ, P2 A) : P2 {x | ∃ A ∈ ℱ, x ∈ A} := by
  simpa using (P2_sUnion (X := X) (ℱ := ℱ) h)