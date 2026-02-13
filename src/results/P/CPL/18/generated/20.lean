

theorem exists_open_subset_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ Topology.P1 U := by
  rcases exists_open_subset_P2 (X := X) (A := A) with ⟨U, hUopen, hAU, hP2U⟩
  exact ⟨U, hUopen, hAU, P2_implies_P1 (A := U) hP2U⟩

theorem P1_inter_interior {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (interior A ∩ interior B) := by
  -- `interior A` and `interior B` are open, hence so is their intersection.
  have h_open : IsOpen (interior A ∩ interior B) :=
    isOpen_interior.inter isOpen_interior
  -- Any open set satisfies `P1`.
  exact P1_of_open (X := X) (A := interior A ∩ interior B) h_open