

theorem exists_P3_between {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P2 A → ∃ B, P3 B ∧ A ⊆ B ∧ B ⊆ interior (closure A) := by
  intro _ hP2
  refine ⟨interior (closure A), ?_, ?_, subset_rfl⟩
  · -- `P3` holds for an open set
    exact P3_of_open (A := interior (closure A)) isOpen_interior
  · -- inclusion `A ⊆ interior (closure A)` follows from `P2 ⟹ P3`
    intro x hxA
    have hP3A : P3 A := P2_implies_P3 (A := A) hP2
    exact hP3A hxA

theorem P3_induction {X : Type*} [TopologicalSpace X] {A : Set X} : (∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A) → P3 A := by
  intro h
  intro x hxA
  rcases h x hxA with ⟨U, hU_open, hxU, hU_sub_cl⟩
  have hU_sub_int : (U : Set X) ⊆ interior (closure A) :=
    interior_maximal hU_sub_cl hU_open
  exact hU_sub_int hxU