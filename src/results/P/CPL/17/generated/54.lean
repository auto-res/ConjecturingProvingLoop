

theorem exists_open_P3_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U, IsOpen U ∧ U ⊆ closure A ∧ Topology.P3 U := by
  refine ⟨interior (closure A), isOpen_interior, interior_subset, ?_⟩
  exact P3_of_open (A := interior (closure A)) isOpen_interior

theorem P2_nhds_basis {X : Type*} [TopologicalSpace X] {A : Set X} : (∀ x ∈ A, ∃ V ∈ 𝓝 x, V ⊆ interior A) → Topology.P2 A := by
  intro h
  intro x hxA
  -- obtain a neighbourhood `V` of `x` contained in `interior A`
  obtain ⟨V, hV_nhds, hV_subset⟩ := h x hxA
  -- refine to an open set `U` with `x ∈ U ⊆ V`
  rcases (mem_nhds_iff.1 hV_nhds) with ⟨U, hU_sub_V, hU_open, hxU⟩
  -- `U` is contained in `interior A`
  have hU_sub_intA : (U : Set X) ⊆ interior A :=
    Set.Subset.trans hU_sub_V hV_subset
  -- hence `U` is contained in `closure (interior A)`
  have hU_sub_cl : (U : Set X) ⊆ closure (interior A) :=
    Set.Subset.trans hU_sub_intA (subset_closure)
  -- an open subset of a closure lies in the corresponding interior
  have hU_sub_intCl : (U : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal hU_sub_cl hU_open
  -- conclude
  exact hU_sub_intCl hxU

theorem P1_prod_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set (X × Y)} : Topology.P1 A ↔ Topology.P1 (Prod.swap ⁻¹' A) := by
  -- Define the homeomorphism that swaps the two factors.
  let e : (Y × X) ≃ₜ (X × Y) := Homeomorph.prodComm Y X
  -- Forward direction: pull back along `e`.
  have h₁ : Topology.P1 A → Topology.P1 (Prod.swap ⁻¹' A) := by
    intro hP1A
    simpa using
      (P1_preimage_homeomorph
          (X := Y × X) (Y := X × Y)
          (e := e) (B := A)) hP1A
  -- Backward direction: pull back along the inverse of `e`
  -- (whose underlying map is again `Prod.swap`).
  have h₂ : Topology.P1 (Prod.swap ⁻¹' A) → Topology.P1 A := by
    intro hP1swap
    simpa using
      (P1_preimage_homeomorph
          (X := X × Y) (Y := Y × X)
          (e := e.symm) (B := Prod.swap ⁻¹' A)) hP1swap
  exact ⟨h₁, h₂⟩

theorem P2_of_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Dense A → Topology.P2 A := by
  intro hP1 hDense
  have hP3 : Topology.P3 A := P3_of_dense (X := X) (A := A) hDense
  exact (P2_iff_P1_and_P3 (A := A)).2 ⟨hP1, hP3⟩

theorem P1_opensUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {U : ι → Set X} : (∀ i, IsOpen (U i)) → Topology.P1 (⋃ i, U i) := by
  intro hU
  have hP1_each : ∀ i, Topology.P1 (U i) := by
    intro i
    exact P1_of_open (A := U i) (hU i)
  simpa using (P1_iUnion (X := X) (f := U) hP1_each)