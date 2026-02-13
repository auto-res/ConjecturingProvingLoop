

theorem P2_iff_P1_and_P3_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (A : Set X)) ↔
      (Topology.P1 (interior (A : Set X)) ∧
        Topology.P3 (interior (A : Set X))) := by
  -- The set `interior A` is open.
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  -- For open sets, `P1` and `P2` are equivalent.
  have h₁ :=
    Topology.P1_iff_P2_of_isOpen
      (X := X) (A := interior (A : Set X)) hOpen
  -- For open sets, `P2` and `P3` are equivalent.
  have h₂ :=
    Topology.P2_iff_P3_of_isOpen
      (X := X) (A := interior (A : Set X)) hOpen
  -- Assemble the desired equivalence.
  constructor
  · intro hP2
    -- Derive `P1` from `P2` using `h₁`.
    have hP1 : Topology.P1 (interior (A : Set X)) := (h₁).2 hP2
    -- Derive `P3` from `P2` using `h₂`.
    have hP3 : Topology.P3 (interior (A : Set X)) := (h₂).1 hP2
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _⟩
    -- Convert `P1` back into `P2` using `h₁`.
    exact (h₁).1 hP1