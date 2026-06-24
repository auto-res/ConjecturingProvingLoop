

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P1 A := by
  intro hP2
  exact Set.Subset.trans hP2 interior_subset

theorem P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A := by
  have h_int : interior A = A := hA.interior_eq
  simpa [P1, h_int] using (subset_closure : A ⊆ closure A)

theorem P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A := by
  -- `A` is open, so its interior is itself
  have h_int : interior A = A := hA.interior_eq
  -- Monotonicity of `interior` gives the desired inclusion
  have h_sub : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  have h_sub' : A ⊆ interior (closure A) := by
    simpa [h_int] using h_sub
  simpa [P2, h_int] using h_sub'

theorem P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A := by
  simpa [P3, hA.interior_eq] using
    (interior_mono (subset_closure : A ⊆ closure A))