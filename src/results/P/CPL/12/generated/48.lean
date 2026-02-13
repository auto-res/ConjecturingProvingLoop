

theorem P2_of_P1_dense {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → Dense (interior A) → P2 A := by
  intro _ hDense x hx
  have hEq : closure (interior (A : Set X)) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [hEq, interior_univ] using (Set.mem_univ x)

theorem P3_of_P1_dense {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → Dense (interior A) → P3 A := by
  intro _hP1 hDense
  intro x hx
  -- The closure of `interior A` is the whole space, by density.
  have h_univ : closure (interior (A : Set X)) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Hence every point belongs to the interior of this closure.
  have hx_int :
      x ∈ interior (closure (interior (A : Set X))) := by
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h_univ, interior_univ] using this
  -- Monotonicity: the interior of `closure (interior A)` is contained in the
  -- interior of `closure A`.
  have h_subset :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (A : Set X)) := by
    have h_cl :
        closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    exact interior_mono h_cl
  exact h_subset hx_int

theorem P2_of_sigma {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} : (∀ i, P2 (A i)) → P2 {x : X | ∃ i, x ∈ A i} := by
  intro hAll
  -- `P2` holds for the indexed union `⋃ i, A i`.
  have hP2Union : P2 (Set.iUnion A) := (P2_iUnion (A := A)) hAll
  -- Identify the two sets.
  have hEq : ({x : X | ∃ i, x ∈ A i} : Set X) = Set.iUnion A := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨i, hxi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact ⟨i, hxi⟩
  -- Transport the property along this equality.
  simpa [hEq] using hP2Union

theorem P2_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} : P2 A → P2 B → P2 C → P2 D → P2 E → P2 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  intro hA hB hC hD hE
  have hABCD : P2 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    P2_prod_four (A := A) (B := B) (C := C) (D := D) hA hB hC hD
  exact
    P2_prod (A := Set.prod (Set.prod (Set.prod A B) C) D) (B := E) hABCD hE