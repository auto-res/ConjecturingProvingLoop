

theorem P2_iff_P1_of_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure A = Set.univ) : Topology.P2 A ↔ Topology.P1 A := by
  -- Since `closure A = univ`, we have `P3 A`.
  have hP3 : Topology.P3 A := P3_of_dense (A := A) h_dense
  -- `P2 A` is equivalent to `P1 A ∧ P3 A`.
  have h₁ : Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) :=
    (P1_and_P3_equiv_P2 (A := A)).symm
  -- Because `P3 A` is true, `P1 A ∧ P3 A` is equivalent to `P1 A`.
  have h₂ : (Topology.P1 A ∧ Topology.P3 A) ↔ Topology.P1 A := by
    constructor
    · intro h; exact h.1
    · intro hP1; exact ⟨hP1, hP3⟩
  -- Combine the two equivalences.
  exact h₁.trans h₂