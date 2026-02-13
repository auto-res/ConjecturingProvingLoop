

theorem Topology.P1_iff_P2_and_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- Equivalences already available for open sets.
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  constructor
  · intro hP1
    -- Deduce `P2` from `P1`, then `P3` from `P2`.
    have hP2 : Topology.P2 A := (h₁).1 hP1
    have hP3 : Topology.P3 A := (h₂).1 hP2
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _hP3⟩
    -- From `P2` we recover `P1` using the first equivalence.
    exact (h₁).2 hP2