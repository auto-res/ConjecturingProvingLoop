

theorem P3_implies_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      (A : Set X) ⊆ interior (closure (interior (closure (A : Set X)))) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  -- Step 1: `A ⊆ interior (closure A)` by `P3`.
  have h₁ : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
  -- Step 2: `interior (closure A)` is contained in the target set.
  have h₂ :
      (interior (closure (A : Set X)) : Set X) ⊆
        interior (closure (interior (closure (A : Set X)))) := by
    -- Basic inclusion into a closure.
    have hSub :
        (interior (closure (A : Set X)) : Set X) ⊆
          closure (interior (closure (A : Set X))) := subset_closure
    -- `interior (closure A)` is open.
    have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    -- Maximality of the interior of a set among open subsets.
    exact interior_maximal hSub hOpen
  -- Combine the two inclusions.
  exact h₁.trans h₂