

theorem Topology.P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P3 A → Topology.P2 A := by
  intro hP1 hP3
  -- First, show that `closure A = closure (interior A)` using `hP1`.
  have h_closure_eq : closure (A : Set X) = closure (interior A) := by
    apply le_antisymm
    ·
      have h_subset : (A : Set X) ⊆ closure (interior A) := hP1
      have : closure (A : Set X) ⊆ closure (closure (interior A)) :=
        closure_mono h_subset
      simpa [closure_closure] using this
    ·
      exact closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- With this equality, use the equivalence to deduce `P2 A` from `hP3`.
  exact (P2_iff_P3_of_closure_eq (X := X) (A := A) h_closure_eq).2 hP3

theorem Topology.P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P1 A ∧ Topology.P3 A := by
  intro hP2
  exact ⟨Topology.P2_implies_P1 (A := A) hP2, Topology.P2_implies_P3 (A := A) hP2⟩