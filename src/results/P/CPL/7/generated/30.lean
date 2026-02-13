

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (interior A) := by
  simpa using P3_of_P2 (A := interior A) P2_interior

theorem P2_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = closure A) : Topology.P2 A ↔ Topology.P3 A := by
  -- First, turn the hypothesis into `P1 A`.
  have hP1 : Topology.P1 A :=
    (P1_iff_closure_interior_eq_closure (A := A)).2 h
  -- Now establish the equivalence between `P2 A` and `P3 A`.
  constructor
  · intro hP2
    exact P1_and_P2_implies_P3 (A := A) ⟨hP1, hP2⟩
  · intro hP3
    exact P1_and_P3_implies_P2 (A := A) ⟨hP1, hP3⟩

theorem subset_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : A ⊆ closure (interior A) := by
  intro x hx
  exact interior_subset (h hx)

theorem closure_interior_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : closure (interior A) = closure (interior (closure A)) := by
  -- First, derive `P1 A` from the given `P2 A`.
  have hP1 : P1 A := P1_of_P2 h
  ------------------------------------------------------------------
  -- 1.  `closure (interior A) ⊆ closure (interior (closure A))`
  ------------------------------------------------------------------
  have h_left : closure (interior A) ⊆ closure (interior (closure A)) := by
    -- Since `interior A ⊆ interior (closure A)`, taking closures yields the claim.
    have h_sub : interior A ⊆ interior (closure (A : Set X)) := by
      have : (A : Set X) ⊆ closure A := subset_closure
      exact interior_mono this
    exact closure_mono h_sub
  ------------------------------------------------------------------
  -- 2.  `closure (interior (closure A)) ⊆ closure (interior A)`
  ------------------------------------------------------------------
  -- First, show the corresponding inclusion for the interiors themselves.
  have h_sub : interior (closure (A : Set X)) ⊆ closure (interior A) := by
    intro x hx
    -- `hx` puts `x` inside `closure A`.
    have hx_cl : x ∈ closure (A : Set X) := interior_subset hx
    -- `P1 A` gives the needed inclusion on closures.
    have h_closure_subset : closure (A : Set X) ⊆ closure (interior A) := by
      -- `closure_mono hP1` yields
      --   `closure A ⊆ closure (closure (interior A))`.
      -- Collapse the double closure on the right.
      have : closure (A : Set X) ⊆ closure (closure (interior A)) :=
        closure_mono hP1
      simpa [closure_closure] using this
    exact h_closure_subset hx_cl
  -- Now, take closures and use `closure_minimal`.
  have h_right : closure (interior (closure (A : Set X))) ⊆
      closure (interior A) := by
    apply closure_minimal h_sub
    exact isClosed_closure
  ------------------------------------------------------------------
  -- 3.  Conclude with antisymmetry.
  ------------------------------------------------------------------
  exact Set.Subset.antisymm h_left h_right

theorem P3_of_local_closure_neighborhoods {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A) : Topology.P3 A := by
  intro x hxA
  rcases h x hxA with ⟨U, hU_open, hxU, hU_subset⟩
  have hU_int : (U : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_maximal hU_subset hU_open
  exact hU_int hxU

theorem P2_of_local_double_closure_neighborhoods {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (interior A)) : Topology.P2 A := by
  intro x hxA
  rcases h x hxA with ⟨U, hU_open, hxU, hU_subset⟩
  have hU_int : (U : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal hU_subset hU_open
  exact hU_int hxU

theorem P2_Union_of_chain {X : Type*} [TopologicalSpace X] {ι : Type*} {F : ι → Set X} (hchain : ∀ i j, F i ⊆ F j ∨ F j ⊆ F i) (hF : ∀ i, Topology.P2 (F i)) : Topology.P2 (⋃ i, F i) := by
  exact P2_Union (F := F) hF