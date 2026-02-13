

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P1 A := by
  intro hA_open
  intro x hx
  have : x ∈ closure (A : Set X) := subset_closure hx
  simpa [hA_open.interior_eq] using this

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A ↔ P1 A ∧ P3 A := by
  constructor
  · intro hP2
    exact ⟨P2_imp_P1 hP2, P2_imp_P3 hP2⟩
  · rintro ⟨hP1, hP3⟩
    exact P2_of_P1_and_P3 hP1 hP3

theorem P3_of_dense_inter {X : Type*} [TopologicalSpace X] {A : Set X} : Dense (interior A) → P3 A := by
  intro hDense
  intro x hxA
  -- `closure (interior A)` is the whole space
  have hClInt : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    (dense_iff_closure_eq).1 hDense
  -- hence `closure A` is also the whole space
  have h_subset : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  have h_univ_sub : (Set.univ : Set X) ⊆ closure A := by
    simpa [hClInt] using h_subset
  have h_closure_sub : closure (A : Set X) ⊆ (Set.univ : Set X) :=
    Set.subset_univ _
  have hClA : closure (A : Set X) = (Set.univ : Set X) :=
    subset_antisymm h_closure_sub h_univ_sub
  -- therefore the interior of `closure A` is the whole space
  have hx_in : (x : X) ∈ interior (closure (A : Set X)) := by
    have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
      trivial
    simpa [hClA, interior_univ] using hx_univ
  exact hx_in