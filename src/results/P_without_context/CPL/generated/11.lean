

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P3 A := by
  intro hP2
  -- `closure (interior A)` is contained in `closure A`
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    have : (interior A) ⊆ A := interior_subset
    exact closure_mono this
  -- combine the two inclusions
  intro x hxA
  exact hsubset (hP2 hxA)

theorem P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A := by
  intro x hxA
  have : x ∈ closure A := subset_closure hxA
  simpa [hA.interior_eq] using this

theorem P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A := by
  intro x hxA
  have h : x ∈ interior (closure A) := (interior_maximal subset_closure hA) hxA
  simpa [hA.interior_eq] using h

theorem closure_inter_interior_eq_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 A) : closure (interior A) = closure A := by
  apply subset_antisymm
  · -- `closure (interior A)` is contained in `closure A`
    exact closure_mono (interior_subset : interior A ⊆ A)
  · -- From `P1`, `A ⊆ closure (interior A)`, and since the latter set is closed,
    -- the minimality of the closure yields the reverse inclusion.
    exact closure_minimal h isClosed_closure

theorem exists_subset_with_P2 {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ Topology.P2 B := by
  refine ⟨interior A, interior_subset, ?_⟩
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using (P2_of_isOpen (A := interior A) h_open)