

theorem P1_prod_closure {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (closure A ×ˢ closure B) := by
  intro hA hB
  -- Upgrade the hypotheses to the closures of `A` and `B`.
  have hA_closure : P1 (closure A) := (P1_closure (A := A)) hA
  have hB_closure : P1 (closure B) := (P1_closure (X := Y) (A := B)) hB
  -- Apply the product lemma.
  simpa using
    (P1_prod (A := closure A) (B := closure B) hA_closure hB_closure)

theorem P3_sUnion_closure {X} [TopologicalSpace X] {ℱ : Set (Set X)} : (∀ A ∈ ℱ, P3 (closure A)) → P3 (⋃₀ ℱ) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℱ, hxA⟩
  have hP3_cl : P3 (closure A) := hAll A hAℱ
  have hx_int : x ∈ interior (closure A) := by
    have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
    simpa [closure_closure] using hP3_cl hx_cl
  have hsubset :
      (interior (closure A) : Set X) ⊆ interior (closure (⋃₀ ℱ)) := by
    have hcl_subset : (closure A : Set X) ⊆ closure (⋃₀ ℱ) := by
      have hA_subset : (A : Set X) ⊆ ⋃₀ ℱ := Set.subset_sUnion_of_mem hAℱ
      exact closure_mono hA_subset
    exact interior_mono hcl_subset
  exact hsubset hx_int

theorem P3_of_interior_dense {X} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P3 A := by
  have hclosure : closure (interior A) = (Set.univ : Set X) := h.closure_eq
  exact P3_of_dense_interior (A := A) hclosure

theorem P2_of_interior_dense {X} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P2 A := by
  have hclosure : closure (interior A) = (Set.univ : Set X) := h.closure_eq
  exact P2_of_dense_interior (A := A) hclosure