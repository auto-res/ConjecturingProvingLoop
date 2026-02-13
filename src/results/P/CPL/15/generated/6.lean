

theorem P2_iterate {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior (closure (interior A))) := by
  simpa using
    (P2_open (A := interior (closure (interior A))) isOpen_interior)

theorem P3_pointwise {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ closure U ⊆ closure A := by
  intro x hx
  have hx_int : x ∈ interior (closure A) := hA hx
  rcases mem_interior.1 hx_int with ⟨U, hU_sub, hU_open, hxU⟩
  have h_closure_subset : (closure U : Set X) ⊆ closure A := by
    have h1 : (closure U : Set X) ⊆ closure (closure A) := closure_mono hU_sub
    simpa [closure_closure] using h1
  exact ⟨U, hU_open, hxU, h_closure_subset⟩

theorem P2_to_iterated_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : A ⊆ closure (interior (closure (interior A))) := by
  exact subset_trans hA
    (subset_closure :
      (interior (closure (interior A)) : Set X) ⊆
        closure (interior (closure (interior A))))

theorem open_imp_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) : P1 A ∧ P2 A ∧ P3 A := by
  exact ⟨P1_open (A := A) h_open, P2_open (A := A) h_open, P3_open (A := A) h_open⟩

theorem clopen_P1_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hcl : IsClosed A) (hop : IsOpen A) : P1 A ↔ P2 A := by
  constructor
  · intro _hP1
    exact P2_open (A := A) hop
  · intro hP2
    exact P1_of_P2 (A := A) hP2