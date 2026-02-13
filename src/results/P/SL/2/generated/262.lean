

theorem Topology.frontier_eq_empty_iff_isClosed_and_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = (∅ : Set X) ↔ (IsClosed A ∧ IsOpen A) := by
  classical
  constructor
  · intro hFrontier
    -- First, show `closure A ⊆ interior A`.
    have hSub : (closure (A : Set X) : Set X) ⊆ interior A := by
      intro x hxCl
      by_cases hxInt : x ∈ interior (A : Set X)
      · exact hxInt
      ·
        -- Otherwise, `x` lies in the frontier, contradicting `frontier A = ∅`.
        have hxFront : x ∈ frontier (A : Set X) := And.intro hxCl hxInt
        have : x ∈ (∅ : Set X) := by
          simpa [hFrontier] using hxFront
        cases this
    -- From the inclusions `interior A ⊆ A ⊆ closure A` and `closure A ⊆ interior A`,
    -- deduce the equalities needed for openness and closedness.
    have hIntEq : interior (A : Set X) = A := by
      apply subset_antisymm
      · exact interior_subset
      · intro x hxA
        have : x ∈ closure (A : Set X) := subset_closure hxA
        exact hSub this
    have hClEq : closure (A : Set X) = A := by
      apply subset_antisymm
      · intro x hxCl
        have : x ∈ interior (A : Set X) := hSub hxCl
        exact interior_subset this
      · exact subset_closure
    -- Conclude that `A` is both closed and open.
    have hClosed : IsClosed (A : Set X) := by
      simpa [hClEq] using (isClosed_closure : IsClosed (closure (A : Set X)))
    have hOpen : IsOpen (A : Set X) := by
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hIntEq] using this
    exact And.intro hClosed hOpen
  · rintro ⟨hClosed, hOpen⟩
    -- Use `closure A = A` and `interior A = A` to rewrite the frontier.
    have hClEq : closure (A : Set X) = A := hClosed.closure_eq
    have hIntEq : interior (A : Set X) = A := hOpen.interior_eq
    simpa [frontier, hClEq, hIntEq, Set.diff_self]