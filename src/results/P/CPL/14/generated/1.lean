

theorem P2_of_open {X} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  -- Since `A` is open, it is contained in the interior of its closure.
  have hx_int_closure : x ∈ interior (closure A) := by
    have h_subset : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal subset_closure hA
    exact h_subset hx
  -- Rewrite `interior (closure (interior A))` using `hA.interior_eq`.
  simpa [hA.interior_eq] using hx_int_closure

theorem P1_of_P2 {X} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 A := by
  intro x hx
  exact interior_subset (h hx)

theorem P3_of_dense_interior {X} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P3 A := by
  intro x hxA
  -- First, show that `closure A` is the whole space.
  have hclosureA : (closure (A : Set X)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · have : (Set.univ : Set X) ⊆ closure A := by
        simpa [h] using (closure_mono (interior_subset : interior A ⊆ A))
      exact this
  -- Hence its interior is also the whole space.
  have hinterior : interior (closure A) = (Set.univ : Set X) := by
    simpa [hclosureA, interior_univ]
  -- Conclude the desired membership.
  simpa [hinterior] using (by
    simp : x ∈ (Set.univ : Set X))

theorem P3_union {X} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_int : x ∈ interior (closure A) := hA hxA
      have hmono : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact hmono hx_int
  | inr hxB =>
      -- `x` comes from `B`
      have hx_int : x ∈ interior (closure B) := hB hxB
      have hmono : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact hmono hx_int

theorem P3_iff_forall_closed_nbhd {X} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x ∈ A, ∃ C, IsClosed C ∧ x ∈ interior C ∧ C ⊆ closure A := by
  -- First, recall the characterization of `P3 A` in terms of open neighbourhoods.
  have h_open : P3 A ↔ ∀ x, x ∈ A → ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A :=
    P3_iff_forall_point
  -- We now build the desired equivalence.
  constructor
  · intro hP3
    -- Use the open–neighbourhood formulation.
    have h := (h_open).1 hP3
    intro x hxA
    rcases h x hxA with ⟨U, hUopen, hxU, hUsubset⟩
    -- Let `C = closure U`.
    refine ⟨closure U, isClosed_closure, ?_, ?_⟩
    · -- `x ∈ interior C`.
      have hU_in_int : (U : Set X) ⊆ interior (closure U) :=
        interior_maximal subset_closure hUopen
      exact hU_in_int hxU
    · -- `C ⊆ closure A`.
      have hCsubset : closure U ⊆ closure A := by
        have h' : closure U ⊆ closure (closure A) := closure_mono hUsubset
        simpa [closure_closure] using h'
      exact hCsubset
  · intro hClosed
    -- Build the open–neighbourhood formulation from the closed one.
    have h : ∀ x, x ∈ A → ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A := by
      intro x hxA
      rcases hClosed x hxA with ⟨C, hCclosed, hxintC, hCsubset⟩
      refine ⟨interior C, isOpen_interior, hxintC, ?_⟩
      exact interior_subset.trans hCsubset
    exact (h_open).2 h