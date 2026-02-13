

theorem P2_implies_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      (A : Set X) ⊆ interior (closure (interior (closure (A : Set X)))) := by
  intro hP2
  -- Step 1 : `A ⊆ interior (closure A)` using an existing lemma.
  have h₁ :
      (A : Set X) ⊆ interior (closure (A : Set X)) :=
    Topology.P2_implies_subset_interior_closure (X := X) (A := A) hP2
  -- Step 2 : `interior (closure A)` is open, hence satisfies `P2`,
  -- giving the desired nested inclusion.
  have h₂ :
      (interior (closure (A : Set X)) : Set X) ⊆
        interior (closure (interior (closure (A : Set X)))) := by
    -- `interior (closure A)` is open.
    have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    -- Every open set satisfies `P2`.
    have hP2' :
        Topology.P2 (interior (closure (A : Set X))) :=
      Topology.isOpen_implies_P2 (X := X)
        (A := interior (closure (A : Set X))) hOpen
    -- Unpack the definition of `P2`.
    dsimp [Topology.P2] at hP2'
    simpa using hP2'
  -- Combine the two inclusions.
  intro x hxA
  have hxB : x ∈ interior (closure (A : Set X)) := h₁ hxA
  exact h₂ hxB