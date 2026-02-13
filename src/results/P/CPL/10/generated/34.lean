

theorem exists_nonempty_closed_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ IsClosed A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), ?_, isClosed_univ, ?_⟩
  ·
    rcases ‹Nonempty X› with ⟨x⟩
    exact ⟨x, by simp⟩
  ·
    simpa using Topology.P1_univ (X := X)

theorem P1_inter_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (closure (interior A) ∩ A) := by
  -- Let `x` be a point of the set `closure (interior A) ∩ A`.
  intro x hx
  -- From the membership we know `x ∈ closure (interior A)`.
  have hx_cl : x ∈ (closure (interior A) : Set X) := hx.1
  -- We show that `interior A ⊆ interior (closure (interior A) ∩ A)`.
  have h_int_subset :
      (interior A : Set X) ⊆ interior (closure (interior A) ∩ A) := by
    -- `interior A` is open …
    have h_open : IsOpen (interior A) := isOpen_interior
    -- … and contained in `closure (interior A) ∩ A`.
    have h_subset : (interior A : Set X) ⊆ closure (interior A) ∩ A := by
      intro y hy
      have hy_cl : y ∈ (closure (interior A) : Set X) := subset_closure hy
      have hy_A : y ∈ (A : Set X) :=
        (interior_subset : (interior A : Set X) ⊆ A) hy
      exact And.intro hy_cl hy_A
    -- By maximality of the interior, the claim follows.
    exact interior_maximal h_subset h_open
  -- Taking closures gives the desired inclusion of closures of interiors.
  have h_closure_subset :
      (closure (interior A) : Set X) ⊆
        closure (interior (closure (interior A) ∩ A)) :=
    closure_mono h_int_subset
  -- Apply this inclusion to `x`.
  exact h_closure_subset hx_cl