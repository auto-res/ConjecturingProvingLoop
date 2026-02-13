

theorem P2_of_frontier_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : frontier A ⊆ interior (closure (interior A))) : P2 A := by
  intro x hxA
  by_cases hx_intA : x ∈ interior A
  · -- `x` already lies in the interior of `A`
    -- and hence in the required interior set.
    have h_subset :
        (interior A : Set X) ⊆ interior (closure (interior A)) := by
      -- `interior A` is open and contained in `closure (interior A)`.
      have h_open : IsOpen (interior A) := isOpen_interior
      exact
        interior_maximal
          (subset_closure :
            (interior A : Set X) ⊆ closure (interior A))
          h_open
    exact h_subset hx_intA
  · -- `x` is **not** in the interior of `A`, hence on the frontier.
    have hx_frontier : x ∈ frontier A := by
      -- `frontier A = closure A \ interior A`.
      change x ∈ closure A \ interior A
      refine And.intro (subset_closure hxA) ?_
      exact hx_intA
    exact h hx_frontier

theorem P2_subsingleton_space {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : P2 A := by
  intro x hx
  -- Since `X` has at most one element, a non-empty subset is the whole space.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; simp
    · intro _
      have : y = x := Subsingleton.elim y x
      simpa [this] using hx
  -- Trivial membership in `univ`.
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  -- Rewrite the goal using `hA_univ`.
  simpa [hA_univ, interior_univ, closure_univ] using hx_univ

theorem P3_subsingleton_space {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : P3 A := by
  intro x hx
  classical
  -- In a subsingleton space, any non-empty subset is the whole space.
  have A_univ : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; simp
    · intro _; 
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Hence `interior (closure A)` is the whole space, so the goal is immediate.
  have : (x : X) ∈ interior (closure A) := by
    have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [A_univ, closure_univ, interior_univ] using hx_univ
  exact this