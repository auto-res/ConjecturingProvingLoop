

theorem P1_imp_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior A) = closure A := by
  exact (P1_iff_closure_inter_eq).1

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, P1 (s i)) → P1 (⋃ i, s i) := by
  intro hP1
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hP1i : P1 (s i) := hP1 i
  have hx_cl : x ∈ closure (interior (s i : Set X)) := hP1i hx_i
  have h_subset :
      closure (interior (s i : Set X))
        ⊆ closure (interior (⋃ j, s j)) := by
    have h_int_sub : interior (s i : Set X) ⊆ interior (⋃ j, s j) := by
      have h_sub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_sub
    exact closure_mono h_int_sub
  exact h_subset hx_cl

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Dense (interior A) → P2 A := by
  intro hDense
  -- The closure of `interior A` is the whole space.
  have hUniv : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    (dense_iff_closure_eq).1 hDense
  -- Hence `P1 A` holds.
  have hP1 : P1 A := by
    intro x hx
    have : (x : X) ∈ (Set.univ : Set X) := by
      trivial
    simpa [hUniv] using this
  -- `P3 A` follows from density.
  have hP3 : P3 A := P3_of_dense_inter hDense
  -- Conclude `P2 A`.
  exact P2_of_P1_and_P3 hP1 hP3