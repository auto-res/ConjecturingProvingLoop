

theorem P2_if_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 A) (hDense : Dense A) : Topology.P2 A := by
  exact (P2_iff_P1_and_P3 (A := A)).2 ⟨h1, P3_of_dense (A := A) hDense⟩

theorem P3_iInter_decreasing {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (hdec : ∀ i j, s j ⊆ s i) (h : ∀ i, Topology.P3 (s i)) : Topology.P3 (⋂ i, s i) := by
  classical
  by_cases hne : (Nonempty ι)
  · -- The index type is non–empty: pick an index `i₀`.
    rcases hne with ⟨i₀⟩
    -- First, identify the intersection with `s i₀`.
    have h_eq : (⋂ i, s i : Set X) = s i₀ := by
      apply Set.Subset.antisymm
      · intro x hx
        exact (Set.mem_iInter.1 hx) i₀
      · intro x hx
        have hx_all : ∀ j, x ∈ s j := by
          intro j
          have h_subset : (s i₀ : Set X) ⊆ s j := hdec j i₀
          exact h_subset hx
        exact (Set.mem_iInter.2 hx_all)
    -- Use the `P3` property for `s i₀` and rewrite using the equality above.
    have hP3_i0 : Topology.P3 (s i₀) := h i₀
    simpa [h_eq] using hP3_i0
  · -- The index type is empty: the intersection is the whole space.
    haveI : IsEmpty ι := ⟨fun i => (hne ⟨i⟩).elim⟩
    have h_eq_univ : (⋂ i, s i : Set X) = (Set.univ : Set X) := by
      ext x
      simp [Set.mem_iInter]
    simpa [h_eq_univ] using (P3_univ (X := X))

theorem P2_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) (hE : Topology.P2 E) : Topology.P2 (Set.prod (Set.prod (Set.prod A B) C) (Set.prod D E)) := by
  -- `P2` for the first two factors `A × B`.
  have hAB : Topology.P2 (Set.prod A B) :=
    P2_prod (X := V) (Y := W) (A := A) (B := B) hA hB
  -- `P2` for the triple product `(A × B) × C`.
  have hABC : Topology.P2 (Set.prod (Set.prod A B) C) :=
    P2_prod (X := V × W) (Y := X) (A := Set.prod A B) (B := C) hAB hC
  -- `P2` for the last two factors `D × E`.
  have hDE : Topology.P2 (Set.prod D E) :=
    P2_prod (X := Y) (Y := Z) (A := D) (B := E) hD hE
  -- Combine the two products.
  simpa using
    (P2_prod (X := (V × W) × X) (Y := Y × Z)
      (A := Set.prod (Set.prod A B) C) (B := Set.prod D E) hABC hDE)

theorem P1_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) (hD : Topology.P1 D) (hE : Topology.P1 E) : Topology.P1 (Set.prod (Set.prod (Set.prod A B) C) (Set.prod D E)) := by
  -- First, obtain `P1` for the product `A × B`.
  have hAB : Topology.P1 (Set.prod A B) :=
    P1_prod (X := V) (Y := W) (A := A) (B := B) hA hB
  -- Next, obtain `P1` for the triple product `(A × B) × C`.
  have hABC : Topology.P1 (Set.prod (Set.prod A B) C) :=
    P1_prod (X := V × W) (Y := X) (A := Set.prod A B) (B := C) hAB hC
  -- `P1` for the product `D × E`.
  have hDE : Topology.P1 (Set.prod D E) :=
    P1_prod (X := Y) (Y := Z) (A := D) (B := E) hD hE
  -- Combine the two products.
  simpa using
    (P1_prod (X := (V × W) × X) (Y := Y × Z)
      (A := Set.prod (Set.prod A B) C) (B := Set.prod D E) hABC hDE)