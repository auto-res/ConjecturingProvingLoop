

theorem P3_iff_P1_and_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Equivalences already established for open sets.
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  -- Assemble the desired equivalence.
  constructor
  · intro hP3
    -- Convert `P3` into `P2`, then into `P1`.
    have hP2 : Topology.P2 A := (h₂).mpr hP3
    have hP1 : Topology.P1 A := (h₁).mpr hP2
    exact And.intro hP1 hP2
  · rintro ⟨_, hP2⟩
    -- Convert `P2` back into `P3` using the second equivalence.
    exact (h₂).mp hP2