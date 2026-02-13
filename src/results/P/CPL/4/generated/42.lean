

theorem P2_Union_monotone_nat_strong {X : Type*} [TopologicalSpace X] {s : ℕ → Set X} (hmono : Monotone s) (hP2 : ∀ n, Topology.P2 (s n)) : Topology.P2 (⋃ n, interior (s n)) := by
  simpa using (P2_countable_Union (X := X) (s := s) hP2)

theorem P1_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP1 : Topology.P1 A) : Topology.P1 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ : Set X) := hA.isOpen_compl
  -- Apply the lemma for open sets.
  simpa using (openSet_P1 (X := X) (A := Aᶜ) hOpen)

theorem P2_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP2 : Topology.P2 A) : Topology.P2 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ : Set X) := hA.isOpen_compl
  simpa using (openSet_P2 (X := X) (A := Aᶜ) hOpen)

theorem P3_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP3 : Topology.P3 A) : Topology.P3 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ : Set X) := hA.isOpen_compl
  simpa using (openSet_P3 (X := X) (A := Aᶜ) hOpen)

theorem P3_of_open_neighborhoods {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ interior (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  rcases h x hxA with ⟨U, _hUopen, hxU, hU_subset⟩
  exact hU_subset hxU